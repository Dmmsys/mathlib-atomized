/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Patrick Massot
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.Algebra.Ring.Fin
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# More operations on modules and ideals related to quotients

## Main results:

- `RingHom.quotientKerEquivRange` : the **first isomorphism theorem** for commutative rings.
- `RingHom.quotientKerEquivRangeS` : the **first isomorphism theorem**
  for a morphism from a commutative ring to a semiring.
- `AlgHom.quotientKerEquivRange` : the **first isomorphism theorem**
  for a morphism of algebras (over a commutative semiring)
- `Ideal.quotientInfRingEquivPiQuotient`: the **Chinese Remainder Theorem**, version for coprime
  ideals (see also `ZMod.prodEquivPi` in `Data.ZMod.Quotient` for elementary versions about
  `ZMod`).
-/

@[expose] public section

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [Ring R] [Semiring S] (f : R →+* S)

/-- The induced map from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotientKerEquivOfRightInverse`) /
is surjective (`quotientKerEquivOfSurjective`).
-/
/-
**RingHom.kerLift** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：kerLift : R ⧸ ker f ->+* S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotientKerEquivOfRightInver
se`) /
is surjective (`quotientKerEquivOfSurjective`).
-/
def kerLift : R ⧸ ker f →+* S :=
  Ideal.Quotient.lift _ f fun _ => mem_ker.mp

@[simp]
/-
**RingHom.kerLift_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：kerLift_mk (r : R) : kerLift f (Ideal.Quotient.mk (ker f) r) = f r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.lift_mk`：lift_mk (f : R ->+* S) (H : forall a : R, a in I
 -> f a = 0) : lift I f H (mk I a) = f a
-/
theorem kerLift_mk (r : R) : kerLift f (Ideal.Quotient.mk (ker f) r) = f r :=
  Ideal.Quotient.lift_mk _ _ _
/-
**RingHom.lift_injective_of_ker_le_ideal** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：lift_injective_of_ker_le_ideal (I : Ideal R) [I.IsTwoSided] {f : R ->+* S}
 (H : forall a : R, a in I -> f a = 0) (hI : ker f <= I) : Function.Injective (I
deal.Quotient.lift I f H)
参数：I : Ideal R；H : forall a : R, a in I -> f a = 0；hI : ker f <= I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `RingHom.ker_eq_bot_iff_eq_zero`：ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ for
all x, f x = 0 -> x = 0
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `Ideal.Quotient.lift_mk`：lift_mk (f : R ->+* S) (H : forall a : R, a in I
 -> f a = 0) : lift I f H (mk I a) = f a
-/
theorem lift_injective_of_ker_le_ideal (I : Ideal R) [I.IsTwoSided]
    {f : R →+* S} (H : ∀ a : R, a ∈ I → f a = 0)
    (hI : ker f ≤ I) : Function.Injective (Ideal.Quotient.lift I f H) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro u hu
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [Ideal.Quotient.lift_mk] at hu
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI (RingHom.mem_ker.mpr hu)

/-- The induced map from the quotient by the kernel is injective. -/
/-
**RingHom.kerLift_injective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：kerLift_injective : Function.Injective (kerLift f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.lift_injective_of_ker_le_ideal`：lift_injective_of_ker_le_ideal (
I : Ideal R) [I.IsTwoSided] {f : R ->+* S} (H : forall a : R, a in I -> f a = 0)
 (hI : ker f <= I) : Functio…
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The induced map from the quotient by the kernel is injective.
-/
theorem kerLift_injective : Function.Injective (kerLift f) :=
  lift_injective_of_ker_le_ideal (ker f) (fun a => by simp only [mem_ker, imp_self]) le_rfl


variable {f}

/-- The **first isomorphism theorem for commutative rings**, computable version. -/
/-
**RingHom.quotientKerEquivOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：quotientKerEquivOfRightInverse {g : S -> R} (hf : Function.RightInverse g 
f) : R ⧸ ker f ≃+* S
参数：hf : Function.RightInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **first isomorphism theorem for commutative rings**, computable version.
-/
def quotientKerEquivOfRightInverse {g : S → R} (hf : Function.RightInverse g f) :
    R ⧸ ker f ≃+* S :=
  { kerLift f with
    toFun := kerLift f
    invFun := Ideal.Quotient.mk (ker f) ∘ g
    left_inv := by
      rintro ⟨x⟩
      apply kerLift_injective
      simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, kerLift_mk,
        Function.comp_apply, hf (f x)]
    right_inv := hf }

@[simp]
/-
**RingHom.quotientKerEquivOfRightInverse.apply** 是 Mathlib 中的一个定理，位于命名空间 `RingHo
m.quotientKerEquivOfRightInverse`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : Ring R] [inst_1 : Semiring S] {f : R →
+* S} {g : S → R}   (hf : Function.RightInverse g ⇑f) (x : R ⧸ RingHom.ker f), (
RingHom.quotientKerEquivOfRightInverse hf) x = f.kerLift x
参数：hf : Function.RightInverse g ⇑f；x : R ⧸ RingHom.ker f；RingHom.quotientKerEqui
vOfRightInverse hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
-/
theorem quotientKerEquivOfRightInverse.apply {g : S → R} (hf : Function.RightInverse g f)
    (x : R ⧸ ker f) : quotientKerEquivOfRightInverse hf x = kerLift f x :=
  rfl

@[simp]
/-
**RingHom.quotientKerEquivOfRightInverse.Symm.apply** 是 Mathlib 中的一个定理，位于命名空间 `R
ingHom.quotientKerEquivOfRightInverse.Symm`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : Ring R] [inst_1 : Semiring S] {f : R →
+* S} {g : S → R}   (hf : Function.RightInverse g ⇑f) (x : S),   (RingHom.quotie
ntKerEquivOfRightInverse hf).symm x = (Ideal.Quotient.mk (RingHom.ker f)) (g x)
参数：hf : Function.RightInverse g ⇑f；x : S；RingHom.quotientKerEquivOfRightInverse 
hf；Ideal.Quotient.mk (RingHom.ker f)；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
-/
theorem quotientKerEquivOfRightInverse.Symm.apply {g : S → R} (hf : Function.RightInverse g f)
    (x : S) : (quotientKerEquivOfRightInverse hf).symm x = Ideal.Quotient.mk (ker f) (g x) :=
  rfl

/-- The **first isomorphism theorem** for commutative rings, surjective case. -/
/-
**RingHom.quotientKerEquivOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：quotientKerEquivOfSurjective (hf : Function.Surjective f) : R ⧸ (ker f) ≃+
* S
参数：hf : Function.Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **first isomorphism theorem** for commutative rings, surjective case.
-/
noncomputable def quotientKerEquivOfSurjective (hf : Function.Surjective f) : R ⧸ (ker f) ≃+* S :=
  quotientKerEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)

@[simp]
/-
**RingHom.quotientKerEquivOfSurjective_apply_mk** 是 Mathlib 中的一个引理，位于命名空间 `RingH
om`。
形式化陈述：quotientKerEquivOfSurjective_apply_mk {f : R ->+* S} (hf : Function.Surjec
tive f) (x : R) : f.quotientKerEquivOfSurjective hf (Ideal.Quotient.mk _ x) = f 
x
参数：hf : Function.Surjective f；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
-/
lemma quotientKerEquivOfSurjective_apply_mk {f : R →+* S} (hf : Function.Surjective f) (x : R) :
    f.quotientKerEquivOfSurjective hf (Ideal.Quotient.mk _ x) = f x :=
  rfl

@[simp]
/-
**RingHom.quotientKerEquivOfSurjective_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rin
gHom`。
形式化陈述：quotientKerEquivOfSurjective_symm_apply {f : R ->+* S} (hf : Function.Surj
ective f) (x : R) : (RingHom.quotientKerEquivOfSurjective hf).symm (f x) = Ideal
.Quotient.mk _ x
参数：hf : Function.Surjective f；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma quotientKerEquivOfSurjective_symm_apply {f : R →+* S} (hf : Function.Surjective f) (x : R) :
    (RingHom.quotientKerEquivOfSurjective hf).symm (f x) = Ideal.Quotient.mk _ x := by
  apply (RingHom.quotientKerEquivOfSurjective hf).injective
  simp
/-
**RingHom.quotientKerEquivOfSurjective_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `Ring
Hom`。
形式化陈述：quotientKerEquivOfSurjective_symm_comp {f : R ->+* S} (hf : Function.Surje
ctive f) : (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom.comp f = Ide
al.Quotient.mk _
参数：hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.quotientKerEquivOfSurjective_symm_apply`：quotientKerEquivOfSurje
ctive_symm_apply {f : R ->+* S} (hf : Function.Surjective f) (x : R) : (RingHom.
quotientKerEquivOfSurjective hf).symm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma quotientKerEquivOfSurjective_symm_comp {f : R →+* S} (hf : Function.Surjective f) :
    (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom.comp f = Ideal.Quotient.mk _ := by
  ext; simp

/-- The **first isomorphism theorem** for commutative rings (`RingHom.rangeS` version). -/
/-
**RingHom.quotientKerEquivRangeS** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：quotientKerEquivRangeS (f : R ->+* S) : R ⧸ ker f ≃+* f.rangeS
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **first isomorphism theorem** for commutative rings (`RingHom.rangeS` versio
n).
-/
noncomputable def quotientKerEquivRangeS (f : R →+* S) : R ⧸ ker f ≃+* f.rangeS :=
  (Ideal.quotEquivOfEq f.ker_rangeSRestrict.symm).trans <|
  quotientKerEquivOfSurjective f.rangeSRestrict_surjective

variable {S : Type v} [Ring S] (f : R →+* S)

/-- The **first isomorphism theorem** for commutative rings (`RingHom.range` version). -/
/-
**RingHom.quotientKerEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：quotientKerEquivRange (f : R ->+* S) : R ⧸ ker f ≃+* f.range
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **first isomorphism theorem** for commutative rings (`RingHom.range` version
).
-/
noncomputable def quotientKerEquivRange (f : R →+* S) : R ⧸ ker f ≃+* f.range :=
  (Ideal.quotEquivOfEq f.ker_rangeRestrict.symm).trans <|
    quotientKerEquivOfSurjective f.rangeRestrict_surjective

end RingHom

namespace Ideal
open Function RingHom

variable {R : Type u} {S : Type v} {F : Type w} [Ring R] [Semiring S]

@[simp]
/-
**Ideal.map_quotient_self** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_quotient_self (I : Ideal R) [I.IsTwoSided] : map (Quotient.mk I) I = ⊥
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
-/
theorem map_quotient_self (I : Ideal R) [I.IsTwoSided] : map (Quotient.mk I) I = ⊥ :=
  eq_bot_iff.2 <|
    Ideal.map_le_iff_le_comap.2 fun _ hx =>
      (Submodule.mem_bot (R ⧸ I)).2 <| Ideal.Quotient.eq_zero_iff_mem.2 hx

@[simp]
/-
**Ideal.mk_ker** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.ker.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Sem
iring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F 
R S] (…
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) = I := by
  ext
  rw [ker, mem_comap, Submodule.mem_bot, Quotient.eq_zero_iff_mem]
/-
**Ideal.map_mk_eq_bot_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_mk_eq_bot_of_le {I J : Ideal R} [J.IsTwoSided] (h : I <= J) : I.map (Q
uotient.mk J) = ⊥
参数：h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_eq_bot_iff_le_ker`：map_eq_bot_iff_le_ker {I : Ideal R} (f : F)
 : I.map f = ⊥ ↔ I <= RingHom.ker f
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
-/
theorem map_mk_eq_bot_of_le {I J : Ideal R} [J.IsTwoSided] (h : I ≤ J) :
    I.map (Quotient.mk J) = ⊥ := by
  rw [map_eq_bot_iff_le_ker, mk_ker]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-
**Ideal.ker_quotient_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ker_quotient_lift {I : Ideal R} [I.IsTwoSided] (f : R ->+* S) (H : I <= ke
r f) : ker (Ideal.Quotient.lift I f H) = (RingHom.ker f).map (Quotient.mk I)
参数：f : R ->+* S；H : I <= ker f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_map_iff_of_surjective`：mem_map_iff_of_surjective {I : Ideal R}
 {y} : y in map f I ↔ exists x, x in I ∧ f x = y
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `Ideal.Quotient.lift_mk`：lift_mk (f : R ->+* S) (H : forall a : R, a in I
 -> f a = 0) : lift I f H (mk I a) = f a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem ker_quotient_lift {I : Ideal R} [I.IsTwoSided] (f : R →+* S)
    (H : I ≤ ker f) :
    ker (Ideal.Quotient.lift I f H) = (RingHom.ker f).map (Quotient.mk I) := by
  apply Ideal.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Quotient.mk_surjective x
    rw [mem_ker, ← hy, Ideal.Quotient.lift_mk, ← mem_ker] at hx
    rw [← hy, mem_map_iff_of_surjective (Quotient.mk I) Quotient.mk_surjective]
    exact ⟨y, hx, rfl⟩
  · intro hx
    rw [mem_map_iff_of_surjective (Quotient.mk I) Quotient.mk_surjective] at hx
    obtain ⟨y, hy⟩ := hx
    rw [mem_ker, ← hy.right, Ideal.Quotient.lift_mk]
    exact hy.left

set_option backward.isDefEq.respectTransparency false in
/-
**Ideal.injective_lift_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：injective_lift_iff {I : Ideal R} [I.IsTwoSided] {f : R ->+* S} (H : forall
 (a : R), a in I -> f a = 0) : Injective (Quotient.lift I f H) ↔ ker f = I
参数：H : forall (a : R), a in I -> f a = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `Ideal.ker_quotient_lift`：ker_quotient_lift {I : Ideal R} [I.IsTwoSided] 
(f : R ->+* S) (H : I <= ker f) : ker (Ideal.Quotient.lift I f H) = (RingHom.ker
 f).map (Quot…
· 使用定理 `Ideal.map_eq_bot_iff_le_ker`：map_eq_bot_iff_le_ker {I : Ideal R} (f : F)
 : I.map f = ⊥ ↔ I <= RingHom.ker f
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma injective_lift_iff {I : Ideal R} [I.IsTwoSided]
    {f : R →+* S} (H : ∀ (a : R), a ∈ I → f a = 0) :
    Injective (Quotient.lift I f H) ↔ ker f = I := by
  rw [injective_iff_ker_eq_bot, ker_quotient_lift, map_eq_bot_iff_le_ker, mk_ker]
  constructor
  · exact fun h ↦ le_antisymm h H
  · rintro rfl; rfl
/-
**Ideal.ker_Pi_Quotient_mk** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：ker_Pi_Quotient_mk {ι : Type*} (I : ι -> Ideal R) [forall i, (I i).IsTwoSi
ded] : ker (RingHom.pi fun i : ι => Quotient.mk (I i)) = ⨅ i, I i
参数：I : ι -> Ideal R；I i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.ker_ringHom`：∀ {S : Type v} [inst : Semiring S] {ι : Type u_3} {R : ι
 → Type u_4} [inst_1 : (i : ι) → Semiring (R i)]   (φ : (i : ι) → S →+* R i), Ri
ngHo…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ker_Pi_Quotient_mk {ι : Type*} (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] :
    ker (RingHom.pi fun i : ι ↦ Quotient.mk (I i)) = ⨅ i, I i := by
  simp [Pi.ker_ringHom, mk_ker]

@[simp]
/-
**Ideal.bot_quotient_isMaximal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：bot_quotient_isMaximal_iff (I : Ideal R) [I.IsTwoSided] : (⊥ : Ideal (R ⧸ 
I)).IsMaximal ↔ I.IsMaximal
参数：I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_isMaximal_of_surjective`：comap_isMaximal_of_surjective (hf :
 Function.Surjective f) {K : Ideal S} [H : IsMaximal K] : IsMaximal (comap f K)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Ideal.bot_isMaximal`：bot_isMaximal : IsMaximal (⊥ : Ideal K)
-/
theorem bot_quotient_isMaximal_iff (I : Ideal R) [I.IsTwoSided] :
    (⊥ : Ideal (R ⧸ I)).IsMaximal ↔ I.IsMaximal :=
  ⟨fun hI =>
    mk_ker (I := I) ▸
      comap_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective (K := ⊥) (H := hI),
    fun hI => by
    let := Quotient.divisionRing I
    exact bot_isMaximal⟩

/-- See also `Ideal.mem_quotient_iff_mem` in case `I ≤ J`. -/
@[simp]
/-
**Ideal.mem_quotient_iff_mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_quotient_iff_mem_sup {I J : Ideal R} [I.IsTwoSided] {x : R} : Quotient
.mk I x in J.map (Quotient.mk I) ↔ x in J ⊔ I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
See also `Ideal.mem_quotient_iff_mem` in case `I ≤ J`.
-/
theorem mem_quotient_iff_mem_sup {I J : Ideal R} [I.IsTwoSided] {x : R} :
    Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J ⊔ I := by
  rw [← mem_comap, comap_map_of_surjective (Quotient.mk I) Quotient.mk_surjective, ←
    ker_eq_comap_bot, mk_ker]

/-- See also `Ideal.mem_quotient_iff_mem_sup` if the assumption `I ≤ J` is not available. -/
/-
**Ideal.mem_quotient_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_quotient_iff_mem {I J : Ideal R} [I.IsTwoSided] (hIJ : I <= J) {x : R}
 : Quotient.mk I x in J.map (Quotient.mk I) ↔ x in J
参数：hIJ : I <= J。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_quotient_iff_mem_sup`：mem_quotient_iff_mem_sup {I J : Ideal R}
 [I.IsTwoSided] {x : R} : Quotient.mk I x in J.map (Quotient.mk I) ↔ x in J ⊔ I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
See also `Ideal.mem_quotient_iff_mem_sup` if the assumption `I ≤ J` is not avail
able.
-/
theorem mem_quotient_iff_mem {I J : Ideal R} [I.IsTwoSided] (hIJ : I ≤ J) {x : R} :
    Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J := by
  rw [mem_quotient_iff_mem_sup, sup_eq_left.mpr hIJ]

section ChineseRemainder
open Function Ideal.Quotient Finset

variable {ι : Type*}

/-- The homomorphism from `R/(⋂ i, f i)` to `∏ i, (R / f i)` featured in the Chinese
  Remainder Theorem. It is bijective if the ideals `f i` are coprime. -/
/-
**Ideal.quotientInfToPiQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientInfToPiQuotient (I : ι -> Ideal R) [forall i, (I i).IsTwoSided] : 
(R ⧸ ⨅ i, I i) ->+* forall i, R ⧸ I i
参数：I : ι -> Ideal R；I i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homomorphism from `R/(⋂ i, f i)` to `∏ i, (R / f i)` featured in the Chinese
  Remainder Theorem. It is bijective if the ideals `f i` are coprime.
-/
def quotientInfToPiQuotient (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] :
    (R ⧸ ⨅ i, I i) →+* ∀ i, R ⧸ I i :=
  Quotient.lift (⨅ i, I i) (RingHom.pi fun i : ι ↦ Quotient.mk (I i))
    (by simp [← RingHom.mem_ker, ker_Pi_Quotient_mk])
/-
**Ideal.quotientInfToPiQuotient_mk** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：quotientInfToPiQuotient_mk (I : ι -> Ideal R) [forall i, (I i).IsTwoSided]
 (x : R) : quotientInfToPiQuotient I (Quotient.mk _ x) = fun i : ι => Quotient.m
k (I i) x
参数：I : ι -> Ideal R；I i；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSidedIInf`：∀ {α : Type u} [inst : Semiring α] {ι : Sort u
_1} (I : ι → Ideal α) [∀ (i : ι), (I i).IsTwoSided], (⨅ i, I i).IsTwoSided
-/
lemma quotientInfToPiQuotient_mk (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] (x : R) :
    quotientInfToPiQuotient I (Quotient.mk _ x) = fun i : ι ↦ Quotient.mk (I i) x :=
  rfl
/-
**Ideal.quotientInfToPiQuotient_mk'** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：quotientInfToPiQuotient_mk' (I : ι -> Ideal R) [forall i, (I i).IsTwoSided
] (x : R) (i : ι) : quotientInfToPiQuotient I (Quotient.mk _ x) i = Quotient.mk 
(I i) x
参数：I : ι -> Ideal R；I i；x : R；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSidedIInf`：∀ {α : Type u} [inst : Semiring α] {ι : Sort u
_1} (I : ι → Ideal α) [∀ (i : ι), (I i).IsTwoSided], (⨅ i, I i).IsTwoSided
-/
lemma quotientInfToPiQuotient_mk' (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] (x : R) (i : ι) :
    quotientInfToPiQuotient I (Quotient.mk _ x) i = Quotient.mk (I i) x :=
  rfl
/-
**Ideal.quotientInfToPiQuotient_inj** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：quotientInfToPiQuotient_inj (I : ι -> Ideal R) [forall i, (I i).IsTwoSided
] : Injective (quotientInfToPiQuotient I)
参数：I : ι -> Ideal R；I i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSidedIInf`：∀ {α : Type u} [inst : Semiring α] {ι : Sort u
_1} (I : ι → Ideal α) [∀ (i : ι), (I i).IsTwoSided], (⨅ i, I i).IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.quotientInfToPiQuotient.eq_1`：∀ {R : Type u} [inst : Ring R] {ι : 
Type u_1} (I : ι → Ideal R) [inst_1 : ∀ (i : ι), (I i).IsTwoSided],   Ideal.quot
ientInfToPiQuotient I = …
· 使用引理 `Ideal.injective_lift_iff`：injective_lift_iff {I : Ideal R} [I.IsTwoSided
] {f : R ->+* S} (H : forall (a : R), a in I -> f a = 0) : Injective (Quotient.l
ift I f H) ↔ k…
· 使用引理 `Ideal.ker_Pi_Quotient_mk`：ker_Pi_Quotient_mk {ι : Type*} (I : ι -> Ideal
 R) [forall i, (I i).IsTwoSided] : ker (RingHom.pi fun i : ι => Quotient.mk (I i
)) = ⨅ i, I i
-/
lemma quotientInfToPiQuotient_inj (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] :
    Injective (quotientInfToPiQuotient I) := by
  rw [quotientInfToPiQuotient, injective_lift_iff, ker_Pi_Quotient_mk]

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
/-
**Ideal.quotientInfToPiQuotient_surj** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：quotientInfToPiQuotient_surj {I : ι -> Ideal R} (hI : Pairwise (IsCoprime 
on I)) : Surjective (quotientInfToPiQuotient I)
参数：hI : Pairwise (IsCoprime on I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Ideal.instIsTwoSidedIInf`：∀ {α : Type u} [inst : Semiring α] {ι : Sort u
_1} (I : ι → Ideal α) [∀ (i : ι), (I i).IsTwoSided], (⨅ i, I i).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.isCoprime_iff_exists`：isCoprime_iff_exists : IsCoprime I J ↔ exist
s i in I, exists j in J, i + j = 1
· 使用定理 `Ideal.isCoprime_biInf`：isCoprime_biInf {J : ι -> Ideal R} {s : Finset ι}
 (hf : forall j in s, IsCoprime I (J j)) : IsCoprime I (⨅ j in s, J j)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_sub_of_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G},
 c + a = b → a = b - c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Ideal.quotientInfToPiQuotient_mk'`：quotientInfToPiQuotient_mk' (I : ι ->
 Ideal R) [forall i, (I i).IsTwoSided] (x : R) (i : ι) : quotientInfToPiQuotient
 I (Quotient.mk _ x) i …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `Fintype.sum_eq_single`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α
] [inst_1 : AddCommMonoid M] {f : α → M} (a : α),   (∀ (x : α), x ≠ a → f x = 0)
 → ∑ x, f x…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
（共 39 条，此处仅展示前 30 条）
-/
lemma quotientInfToPiQuotient_surj {I : ι → Ideal R}
    (hI : Pairwise (IsCoprime on I)) : Surjective (quotientInfToPiQuotient I) := by
  classical
  cases nonempty_fintype ι
  intro g
  choose f hf using fun i ↦ mk_surjective (g i)
  have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
      intro j hj
      exact hI (by simpa [ne_comm, isCoprime_iff_add] using hj)
    rcases isCoprime_iff_exists.mp (isCoprime_biInf hI') with ⟨u, hu, e, he, hue⟩
    replace he : ∀ j, j ≠ i → e ∈ I j := by simpa using he
    refine ⟨e, ?_, ?_⟩
    · simp [eq_sub_of_add_eq' hue, map_sub, eq_zero_iff_mem.mpr hu]
    · exact fun j hj ↦ eq_zero_iff_mem.mpr (he j hj)
  choose e he using key
  use mk _ (∑ i, f i * e i)
  ext i
  rw [quotientInfToPiQuotient_mk', map_sum, Fintype.sum_eq_single i]
  · simp [(he i).1, hf]
  · intro j hj
    simp [(he j).2 i hj.symm]

/-- **Chinese Remainder Theorem**. Eisenbud Ex.2.6.
Similar to Atiyah-Macdonald 1.10 and Stacks 00DT -/
@[wikidata Q193878]
/-
**Ideal.quotientInfRingEquivPiQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientInfRingEquivPiQuotient (f : ι -> Ideal R) (hf : Pairwise (IsCoprim
e on f)) : (R ⧸ ⨅ i, f i) ≃+* forall i, R ⧸ f i
参数：f : ι -> Ideal R；hf : Pairwise (IsCoprime on f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Chinese Remainder Theorem**. Eisenbud Ex.2.6.
Similar to Atiyah-Macdonald 1.10 and Stacks 00DT
-/
noncomputable def quotientInfRingEquivPiQuotient (f : ι → Ideal R)
    (hf : Pairwise (IsCoprime on f)) : (R ⧸ ⨅ i, f i) ≃+* ∀ i, R ⧸ f i :=
  { Equiv.ofBijective _ ⟨quotientInfToPiQuotient_inj f, quotientInfToPiQuotient_surj hf⟩,
    quotientInfToPiQuotient f with }

/-- Corollary of Chinese Remainder Theorem: if `Iᵢ` are pairwise coprime ideals in a
commutative ring then the canonical map `R → ∏ (R ⧸ Iᵢ)` is surjective. -/
/-
**Ideal.pi_quotient_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：pi_quotient_surjective {I : ι -> Ideal R} (hf : Pairwise (IsCoprime on I))
 (x : (i : ι) -> R ⧸ I i) : exists r : R, forall i, r = x i
参数：hf : Pairwise (IsCoprime on I)；x : (i : ι) -> R ⧸ I i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSidedIInf`：∀ {α : Type u} [inst : Semiring α] {ι : Sort u
_1} (I : ι → Ideal α) [∀ (i : ι), (I i).IsTwoSided], (⨅ i, I i).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `Ideal.quotientInfToPiQuotient_surj`：quotientInfToPiQuotient_surj {I : ι 
-> Ideal R} (hI : Pairwise (IsCoprime on I)) : Surjective (quotientInfToPiQuotie
nt I)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)

--- 原说明 ---
Corollary of Chinese Remainder Theorem: if `Iᵢ` are pairwise coprime ideals in a
commutative ring then the canonical map `R → ∏ (R ⧸ Iᵢ)` is surjective.
-/
lemma pi_quotient_surjective {I : ι → Ideal R}
    (hf : Pairwise (IsCoprime on I)) (x : (i : ι) → R ⧸ I i) :
    ∃ r : R, ∀ i, r = x i := by
  obtain ⟨y, rfl⟩ := Ideal.quotientInfToPiQuotient_surj hf x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨r, fun i ↦ rfl⟩
/-
**Ideal.pi_mkQ_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：pi_mkQ_surjective {I : ι -> Ideal R} (hI : Pairwise (IsCoprime on I)) : Su
rjective (LinearMap.pi fun i => (I i).mkQ)
参数：hI : Pairwise (IsCoprime on I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `Ideal.pi_quotient_surjective`：pi_quotient_surjective {I : ι -> Ideal R} 
(hf : Pairwise (IsCoprime on I)) (x : (i : ι) -> R ⧸ I i) : exists r : R, forall
 i, r = x i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma pi_mkQ_surjective {I : ι → Ideal R} (hI : Pairwise (IsCoprime on I)) :
    Surjective (LinearMap.pi fun i ↦ (I i).mkQ) :=
  fun x ↦ have ⟨r, eq⟩ := pi_quotient_surjective hI x; ⟨r, funext eq⟩

-- variant of `IsDedekindDomain.exists_forall_sub_mem_ideal` which doesn't assume Dedekind domain!
/-- Corollary of Chinese Remainder Theorem: if `Iᵢ` are pairwise coprime ideals in a
commutative ring then given elements `xᵢ` you can find `r` with `r - xᵢ ∈ Iᵢ` for all `i`. -/
/-
**Ideal.exists_forall_sub_mem_ideal** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：exists_forall_sub_mem_ideal {I : ι -> Ideal R} (hI : Pairwise (IsCoprime o
n I)) (x : ι -> R) : exists r : R, forall i, r - x i in I i
参数：hI : Pairwise (IsCoprime on I)；x : ι -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `Ideal.pi_quotient_surjective`：pi_quotient_surjective {I : ι -> Ideal R} 
(hf : Pairwise (IsCoprime on I)) (x : (i : ι) -> R ⧸ I i) : exists r : R, forall
 i, r = x i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…

--- 原说明 ---
Corollary of Chinese Remainder Theorem: if `Iᵢ` are pairwise coprime ideals in a
commutative ring then given elements `xᵢ` you can find `r` with `r - xᵢ ∈ Iᵢ` fo
r all `i`.
-/
lemma exists_forall_sub_mem_ideal
    {I : ι → Ideal R} (hI : Pairwise (IsCoprime on I)) (x : ι → R) :
    ∃ r : R, ∀ i, r - x i ∈ I i := by
  obtain ⟨y, hy⟩ := Ideal.pi_quotient_surjective hI (fun i ↦ x i)
  exact ⟨y, fun i ↦ (Submodule.Quotient.eq (I i)).mp <| hy i⟩

/-- **Chinese remainder theorem**, specialized to two ideals. -/
/-
**Ideal.quotientInfEquivQuotientProd** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) : R
 ⧸ I ⊓ J ≃+* (R ⧸ I) × R ⧸ J
参数：I J : Ideal R；coprime : IsCoprime I J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Chinese remainder theorem**, specialized to two ideals.
-/
noncomputable def quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    R ⧸ I ⊓ J ≃+* (R ⧸ I) × R ⧸ J :=
  let f : Fin 2 → Ideal R := ![I, J]
  have hf : Pairwise (IsCoprime on f) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> try contradiction
    · assumption
    · exact coprime.symm
  (Ideal.quotEquivOfEq (by simp [f, iInf, inf_comm])).trans <|
            (Ideal.quotientInfRingEquivPiQuotient f hf).trans <| RingEquiv.piFinTwo fun i => R ⧸ f i

@[simp]
/-
**Ideal.quotientInfEquivQuotientProd_fst** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientInfEquivQuotientProd_fst (I J : Ideal R) (coprime : IsCoprime I J)
 (x : R ⧸ I ⊓ J) : (quotientInfEquivQuotientProd I J coprime x).fst = Ideal.Quot
ient.factor inf_le_left x
参数：I J : Ideal R；coprime : IsCoprime I J；x : R ⧸ I ⊓ J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem quotientInfEquivQuotientProd_fst (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J) :
    (quotientInfEquivQuotientProd I J coprime x).fst =
      Ideal.Quotient.factor inf_le_left x :=
  Quot.inductionOn x fun _ => rfl

@[simp]
/-
**Ideal.quotientInfEquivQuotientProd_snd** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientInfEquivQuotientProd_snd (I J : Ideal R) (coprime : IsCoprime I J)
 (x : R ⧸ I ⊓ J) : (quotientInfEquivQuotientProd I J coprime x).snd = Ideal.Quot
ient.factor inf_le_right x
参数：I J : Ideal R；coprime : IsCoprime I J；x : R ⧸ I ⊓ J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem quotientInfEquivQuotientProd_snd (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J) :
    (quotientInfEquivQuotientProd I J coprime x).snd =
      Ideal.Quotient.factor inf_le_right x :=
  Quot.inductionOn x fun _ => rfl

@[simp]
/-
**Ideal.fst_comp_quotientInfEquivQuotientProd** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：fst_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime
 I J) : (RingHom.fst _ _).comp (quotientInfEquivQuotientProd I J coprime : R ⧸ I
 ⊓ J ->+* (R ⧸ I) × R ⧸ J) = Ideal.Quotient.factor inf_le_left
参数：I J : Ideal R；coprime : IsCoprime I J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem fst_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    (RingHom.fst _ _).comp
        (quotientInfEquivQuotientProd I J coprime : R ⧸ I ⊓ J →+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor inf_le_left := by
  apply Quotient.ringHom_ext; ext; rfl

@[simp]
/-
**Ideal.snd_comp_quotientInfEquivQuotientProd** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：snd_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime
 I J) : (RingHom.snd _ _).comp (quotientInfEquivQuotientProd I J coprime : R ⧸ I
 ⊓ J ->+* (R ⧸ I) × R ⧸ J) = Ideal.Quotient.factor inf_le_right
参数：I J : Ideal R；coprime : IsCoprime I J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem snd_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    (RingHom.snd _ _).comp
        (quotientInfEquivQuotientProd I J coprime : R ⧸ I ⊓ J →+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor inf_le_right := by
  apply Quotient.ringHom_ext; ext; rfl

/-- **Chinese remainder theorem**, specialized to two ideals. -/
/-
**Ideal.quotientMulEquivQuotientProd** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) : R
 ⧸ I * J ≃+* (R ⧸ I) × R ⧸ J
参数：I J : Ideal R；coprime : IsCoprime I J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Chinese remainder theorem**, specialized to two ideals.
-/
noncomputable def quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    R ⧸ I * J ≃+* (R ⧸ I) × R ⧸ J :=
  Ideal.quotEquivOfEq (mul_eq_inf_of_isCoprime coprime) |>.trans <|
    Ideal.quotientInfEquivQuotientProd I J coprime

@[simp]
/-
**Ideal.quotientMulEquivQuotientProd_fst** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientMulEquivQuotientProd_fst (I J : Ideal R) (coprime : IsCoprime I J)
 (x : R ⧸ I * J) : (quotientMulEquivQuotientProd I J coprime x).fst = Ideal.Quot
ient.factor mul_le_left x
参数：I J : Ideal R；coprime : IsCoprime I J；x : R ⧸ I * J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.mul_le_left`：mul_le_left [I.IsTwoSided] : I * J <= I
-/
theorem quotientMulEquivQuotientProd_fst (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I * J) :
    (quotientMulEquivQuotientProd I J coprime x).fst =
      Ideal.Quotient.factor mul_le_left x :=
  Quot.inductionOn x fun _ => rfl

@[simp]
/-
**Ideal.quotientMulEquivQuotientProd_snd** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientMulEquivQuotientProd_snd (I J : Ideal R) (coprime : IsCoprime I J)
 (x : R ⧸ I * J) : (quotientMulEquivQuotientProd I J coprime x).snd = Ideal.Quot
ient.factor mul_le_right x
参数：I J : Ideal R；coprime : IsCoprime I J；x : R ⧸ I * J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.mul_le_right`：mul_le_right : I * J <= J
-/
theorem quotientMulEquivQuotientProd_snd (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I * J) :
    (quotientMulEquivQuotientProd I J coprime x).snd =
      Ideal.Quotient.factor mul_le_right x :=
  Quot.inductionOn x fun _ => rfl

@[simp]
/-
**Ideal.fst_comp_quotientMulEquivQuotientProd** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：fst_comp_quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime
 I J) : (RingHom.fst _ _).comp (quotientMulEquivQuotientProd I J coprime : R ⧸ I
 * J ->+* (R ⧸ I) × R ⧸ J) = Ideal.Quotient.factor mul_le_left
参数：I J : Ideal R；coprime : IsCoprime I J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Ideal.mul_le_left`：mul_le_left [I.IsTwoSided] : I * J <= I
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem fst_comp_quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    (RingHom.fst _ _).comp
        (quotientMulEquivQuotientProd I J coprime : R ⧸ I * J →+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor mul_le_left := by
  apply Quotient.ringHom_ext; ext; rfl

@[simp]
/-
**Ideal.snd_comp_quotientMulEquivQuotientProd** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：snd_comp_quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime
 I J) : (RingHom.snd _ _).comp (quotientMulEquivQuotientProd I J coprime : R ⧸ I
 * J ->+* (R ⧸ I) × R ⧸ J) = Ideal.Quotient.factor mul_le_right
参数：I J : Ideal R；coprime : IsCoprime I J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Ideal.mul_le_right`：mul_le_right : I * J <= J
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem snd_comp_quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    (RingHom.snd _ _).comp
        (quotientMulEquivQuotientProd I J coprime : R ⧸ I * J →+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor mul_le_right := by
  apply Quotient.ringHom_ext; ext; rfl

end ChineseRemainder

section QuotientAlgebra

variable (R₁ R₂ : Type*) {A B : Type*}
variable [CommSemiring R₁] [CommSemiring R₂] [Ring A]
variable [Algebra R₁ A] [Algebra R₂ A]

/-- The `R₁`-algebra structure on `A/I` for an `R₁`-algebra `A` -/
/-
**Ideal.Quotient.algebra** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：(R₁ : Type u_1) →   {A : Type u_3} →     [inst : CommSemiring R₁] →       
[inst_1 : Ring A] → [Algebra R₁ A] → {I : Ideal A} → [inst_3 : I.IsTwoSided] → A
lgebra R₁ (A ⧸ I)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R₁`-algebra structure on `A/I` for an `R₁`-algebra `A`
-/
instance Quotient.algebra {I : Ideal A} [I.IsTwoSided] : Algebra R₁ (A ⧸ I) where
  algebraMap := (Ideal.Quotient.mk I).comp (algebraMap R₁ A)
  smul_def' := fun _ x =>
    Quotient.inductionOn' x fun _ =>
      ((Quotient.mk I).congr_arg <| Algebra.smul_def _ _).trans (map_mul _ _ _)
  commutes' := by rintro r ⟨x⟩; exact congr_arg (⟦·⟧) (Algebra.commutes r x)
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A} [CommRing A] [Algebra R₁ A] (I : Ideal A) : Algebra R₁ (A ⧸ I) := inferInstance

-- This instance can be inferred, but is kept around as a useful shortcut.
/-
**Ideal.Quotient.isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Type u_3} [inst : CommSemiring R₁] 
[inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [inst_3 : Algebra R₁ A] [inst_4 :
 Algebra R₂ A] [inst_5 : SMul R₁ R₂] [IsScalarTower R₁ R₂ A] (I : Ideal A),   Is
ScalarTower R₁ R₂ (A ⧸ I)
参数：R₁ : Type u_1；R₂ : Type u_2；I : Ideal A；A ⧸ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
instance Quotient.isScalarTower [SMul R₁ R₂] [IsScalarTower R₁ R₂ A] (I : Ideal A) :
    IsScalarTower R₁ R₂ (A ⧸ I) := inferInstance

/-- The canonical morphism `A →ₐ[R₁] A ⧸ I` as morphism of `R₁`-algebras, for `I` an ideal of
`A`, where `A` is an `R₁`-algebra. -/
/-
**Ideal.Quotient.mk** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：mk : R ->+* R ⧸ I where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `A →ₐ[R₁] A ⧸ I` as morphism of `R₁`-algebras, for `I` an
 ideal of
`A`, where `A` is an `R₁`-algebra.
-/
def Quotient.mkₐ (I : Ideal A) [I.IsTwoSided] : A →ₐ[R₁] A ⧸ I :=
  ⟨⟨⟨⟨fun a => Submodule.Quotient.mk a, rfl⟩, fun _ _ => rfl⟩, rfl, fun _ _ => rfl⟩, fun _ => rfl⟩
/-
**Ideal.Quotient.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：∀ (R₁ : Type u_1) {A : Type u_3} [inst : CommSemiring R₁] [inst_1 : Ring A
] [inst_2 : Algebra R₁ A] {I : Ideal A}   [inst_3 : I.IsTwoSided] {S : Type u_5}
 [inst_4 : Semiring S] [inst_5 : Algebra R₁ S] ⦃f g : A ⧸ I →ₐ[R₁] S⦄,   f.comp 
(Ideal.Quotient.mkₐ R₁ I) = g.comp (Ideal.Quotient.mkₐ R₁ I) → f = g
参数：R₁ : Type u_1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
-/
theorem Quotient.algHom_ext {I : Ideal A} [I.IsTwoSided]
    {S} [Semiring S] [Algebra R₁ S] ⦃f g : A ⧸ I →ₐ[R₁] S⦄
    (h : f.comp (Quotient.mkₐ R₁ I) = g.comp (Quotient.mkₐ R₁ I)) : f = g :=
  AlgHom.ext fun x => Quotient.inductionOn' x <| AlgHom.congr_fun h
/-
**Ideal.Quotient.alg_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：∀ (R₁ : Type u_1) [inst : CommSemiring R₁] {A : Type u_5} [inst_1 : CommRi
ng A] [inst_2 : Algebra R₁ A] (I : Ideal A),   algebraMap R₁ (A ⧸ I) = (algebraM
ap A (A ⧸ I)).comp (algebraMap R₁ A)
参数：R₁ : Type u_1；I : Ideal A；A ⧸ I；algebraMap A (A ⧸ I)；algebraMap R₁ A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.alg_map_eq {A} [CommRing A] [Algebra R₁ A] (I : Ideal A) :
    algebraMap R₁ (A ⧸ I) = (algebraMap A (A ⧸ I)).comp (algebraMap R₁ A) :=
  rfl
/-
**Ideal.Quotient.mk** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：mk : R ->+* R ⧸ I where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.mkₐ_toRingHom (I : Ideal A) [I.IsTwoSided] :
    (Quotient.mkₐ R₁ I).toRingHom = Ideal.Quotient.mk I :=
  rfl

@[simp]
/-
**Ideal.Quotient.mk** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：mk : R ->+* R ⧸ I where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.mkₐ_eq_mk (I : Ideal A) [I.IsTwoSided] : ⇑(Quotient.mkₐ R₁ I) = Quotient.mk I :=
  rfl

@[simp]
/-
**Ideal.Quotient.algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：∀ {R : Type u_5} [inst : CommRing R] (I : Ideal R), algebraMap R (R ⧸ I) =
 Ideal.Quotient.mk I
参数：I : Ideal R；R ⧸ I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.algebraMap_eq {R} [CommRing R] (I : Ideal R) :
    algebraMap R (R ⧸ I) = Quotient.mk I :=
  rfl

@[simp]
/-
**Ideal.Quotient.mk_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：∀ (R₁ : Type u_1) {A : Type u_3} [inst : CommSemiring R₁] [inst_1 : Ring A
] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst_3 : I.IsTwoSided], (Ideal.Quotie
nt.mk I).comp (algebraMap R₁ A) = algebraMap R₁ (A ⧸ I)
参数：R₁ : Type u_1；I : Ideal A；Ideal.Quotient.mk I；algebraMap R₁ A；A ⧸ I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.mk_comp_algebraMap (I : Ideal A) [I.IsTwoSided] :
    (Quotient.mk I).comp (algebraMap R₁ A) = algebraMap R₁ (A ⧸ I) :=
  rfl

@[simp]
/-
**Ideal.Quotient.mk_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：∀ (R₁ : Type u_1) {A : Type u_3} [inst : CommSemiring R₁] [inst_1 : Ring A
] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst_3 : I.IsTwoSided] (x : R₁), (Ide
al.Quotient.mk I) ((algebraMap R₁ A) x) = (algebraMap R₁ (A ⧸ I)) x
参数：R₁ : Type u_1；I : Ideal A；x : R₁；Ideal.Quotient.mk I；(algebraMap R₁ A) x；alge
braMap R₁ (A ⧸ I)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.mk_algebraMap (I : Ideal A) [I.IsTwoSided] (x : R₁) :
    Quotient.mk I (algebraMap R₁ A x) = algebraMap R₁ (A ⧸ I) x :=
  rfl

/-- The canonical morphism `A →ₐ[R₁] I.quotient` is surjective. -/
/-
**Ideal.Quotient.mk** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：mk : R ->+* R ⧸ I where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `A →ₐ[R₁] I.quotient` is surjective.
-/
theorem Quotient.mkₐ_surjective (I : Ideal A) [I.IsTwoSided] :
    Function.Surjective (Quotient.mkₐ R₁ I) :=
  Quot.mk_surjective

/-- The kernel of `A →ₐ[R₁] I.quotient` is `I`. -/
@[simp]
/-
**Ideal.Quotient.mk** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：mk : R ->+* R ⧸ I where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of `A →ₐ[R₁] I.quotient` is `I`.
-/
theorem Quotient.mkₐ_ker (I : Ideal A) [I.IsTwoSided] :
    RingHom.ker (Quotient.mkₐ R₁ I : A →+* A ⧸ I) = I :=
  Ideal.mk_ker
/-
**Ideal.Quotient.mk_bijective_iff_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotie
nt`。
形式化陈述：∀ {A : Type u_3} [inst : Ring A] (I : Ideal A) [inst_1 : I.IsTwoSided],   
Function.Bijective ⇑(Ideal.Quotient.mk I) ↔ I = ⊥
参数：I : Ideal A；Ideal.Quotient.mk I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_eq_bot_iff_of_injective`：map_eq_bot_iff_of_injective {I : Idea
l R} {f : F} (hf : Function.Injective f) : I.map f = ⊥ ↔ I = ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.map_eq_bot_iff_le_ker`：map_eq_bot_iff_le_ker {I : Ideal R} (f : F)
 : I.map f = ⊥ ↔ I <= RingHom.ker f
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
-/
lemma Quotient.mk_bijective_iff_eq_bot (I : Ideal A) [I.IsTwoSided] :
    Function.Bijective (mk I) ↔ I = ⊥ := by
  constructor
  · intro h
    rw [← map_eq_bot_iff_of_injective h.1]
    exact (map_eq_bot_iff_le_ker _).mpr <| le_of_eq mk_ker.symm
  · exact fun h => ⟨(injective_iff_ker_eq_bot _).mpr <| by rw [mk_ker, h], mk_surjective⟩

section

/-- `AlgHom` version of `Ideal.Quotient.factor`. -/
/-
**Ideal.Quotient.factor** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：factor (H : S <= T) : R ⧸ S ->+* R ⧸ T
参数：H : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgHom` version of `Ideal.Quotient.factor`.
-/
def Quotient.factorₐ {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (hIJ : I ≤ J) :
    A ⧸ I →ₐ[R₁] A ⧸ J where
  __ := Ideal.Quotient.factor hIJ
  commutes' _ := rfl

variable {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (hIJ : I ≤ J)

@[simp]
/-
**Ideal.Quotient.coe_factor** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Quotient.coe_factorₐ :
    (Ideal.Quotient.factorₐ R₁ hIJ : A ⧸ I →+* A ⧸ J) = Ideal.Quotient.factor hIJ := rfl

@[simp]
/-
**Ideal.Quotient.factor** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：factor (H : S <= T) : R ⧸ S ->+* R ⧸ T
参数：H : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Quotient.factorₐ_apply_mk (x : A) :
    Ideal.Quotient.factorₐ R₁ hIJ x = x := rfl

@[simp]
/-
**Ideal.Quotient.factor** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：factor (H : S <= T) : R ⧸ S ->+* R ⧸ T
参数：H : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Quotient.factorₐ_comp_mk :
    (Ideal.Quotient.factorₐ R₁ hIJ).comp (Ideal.Quotient.mkₐ R₁ I) = Ideal.Quotient.mkₐ R₁ J := rfl

@[simp]
/-
**Ideal.Quotient.factor** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：factor (H : S <= T) : R ⧸ S ->+* R ⧸ T
参数：H : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.factorₐ_apply (x : A ⧸ I) :
    Quotient.factorₐ R₁ hIJ x = Quotient.factor hIJ x := rfl

@[simp]
/-
**Ideal.Quotient.factor** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：factor (H : S <= T) : R ⧸ S ->+* R ⧸ T
参数：H : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Quotient.factorₐ_refl {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) :
    Ideal.Quotient.factorₐ R (le_refl I) = AlgHom.id R _ := by
  ext
  simp

@[simp]
/-
**Ideal.Quotient.factor** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：factor (H : S <= T) : R ⧸ S ->+* R ⧸ T
参数：H : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Quotient.factorₐ_comp {K : Ideal A} [K.IsTwoSided] (hJK : J ≤ K) :
    (Ideal.Quotient.factorₐ R₁ hJK).comp (Ideal.Quotient.factorₐ R₁ hIJ) =
      Ideal.Quotient.factorₐ R₁ (hIJ.trans hJK) :=
  Ideal.Quotient.algHom_ext _ (by ext; simp)

end

variable {R₁}

section

variable [Semiring B] [Algebra R₁ B]

set_option backward.isDefEq.respectTransparency false in
/-- `Ideal.quotient.lift` as an `AlgHom`. -/
/-
**Ideal.Quotient.lift** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：lift (f : R ->+* S) (H : forall a : R, a in I -> f a = 0) : R ⧸ I ->+* S
参数：f : R ->+* S；H : forall a : R, a in I -> f a = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ideal.quotient.lift` as an `AlgHom`.
-/
def Quotient.liftₐ (I : Ideal A) [I.IsTwoSided] (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) :
    A ⧸ I →ₐ[R₁] B :=
  { -- this is IsScalarTower.algebraMap_apply R₁ A (A ⧸ I) but the file `Algebra.Algebra.Tower`
    -- imports this file.
      Ideal.Quotient.lift
      I (f : A →+* B) hI with
    commutes' := fun r => by
      have : algebraMap R₁ (A ⧸ I) r = Ideal.Quotient.mk I (algebraMap R₁ A r) := rfl
      rw [this, RingHom.toFun_eq_coe, Ideal.Quotient.lift_mk,
        AlgHom.coe_toRingHom, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        map_smul, map_one] }

@[simp]
/-
**Ideal.Quotient.lift** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：lift (f : R ->+* S) (H : forall a : R, a in I -> f a = 0) : R ⧸ I ->+* S
参数：f : R ->+* S；H : forall a : R, a in I -> f a = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.liftₐ_apply (I : Ideal A) [I.IsTwoSided]
    (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) (x) :
    Ideal.Quotient.liftₐ I f hI x = Ideal.Quotient.lift I (f : A →+* B) hI x :=
  rfl
/-
**Ideal.Quotient.lift** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：lift (f : R ->+* S) (H : forall a : R, a in I -> f a = 0) : R ⧸ I ->+* S
参数：f : R ->+* S；H : forall a : R, a in I -> f a = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.liftₐ_comp (I : Ideal A) [I.IsTwoSided]
    (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) :
    (Ideal.Quotient.liftₐ I f hI).comp (Ideal.Quotient.mkₐ R₁ I) = f :=
  AlgHom.ext fun _ => (Ideal.Quotient.lift_mk I (f : A →+* B) hI :)
/-
**Ideal.Quotient.span_singleton_one** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：∀ {A : Type u_3} [inst : Ring A] (I : Ideal A) [I.IsTwoSided], A ∙ 1 = ⊤
参数：I : Ideal A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Submodule.range_mkQ`：range_mkQ : range p.mkQ = ⊤
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Ideal.span_singleton_one`：span_singleton_one : span ({1} : Set α) = ⊤
· 使用定理 `Ideal.span.eq_1`：∀ {α : Type u} [inst : Semiring α] (s : Set α), Ideal.s
pan s = Submodule.span α s
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `Ideal.Quotient.mk_eq_mk`：mk_eq_mk (x : R) : (Submodule.Quotient.mk x : R
 ⧸ I) = mk I x
-/
theorem Quotient.span_singleton_one (I : Ideal A) [I.IsTwoSided] :
    Submodule.span A {(1 : A ⧸ I)} = ⊤ := by
  rw [← map_one (mk _), ← Submodule.range_mkQ I, ← Submodule.map_top, ← Ideal.span_singleton_one,
    Ideal.span, Submodule.map_span, Set.image_singleton, Submodule.mkQ_apply, Quotient.mk_eq_mk]

open scoped Pointwise in
/-
**Ideal.Quotient.smul_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：∀ {R : Type u_5} [inst : CommRing R] (a : R) (I : Ideal R), a • ⊤ = R ∙ Su
bmodule.Quotient.mk a
参数：a : R；I : Ideal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.smul_span`：smul_span (a : α) (s : Set M) : a • span R s = span
 R (a • s)
· 使用引理 `Set.smul_set_singleton`：smul_set_singleton : a • ({b} : Set β) = {a • b}
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Quotient.smul_top {R : Type*} [CommRing R] (a : R) (I : Ideal R) :
    (a • ⊤ : Submodule R (R ⧸ I)) = Submodule.span R {Submodule.Quotient.mk a} := by
  simp [← Ideal.Quotient.span_singleton_one, Algebra.smul_def, Submodule.smul_span]
/-
**Ideal.KerLift.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.KerLift`。
形式化陈述：∀ {R₁ : Type u_1} {A : Type u_3} {B : Type u_4} [inst : CommSemiring R₁] [
inst_1 : Ring A] [inst_2 : Algebra R₁ A]   [inst_3 : Semiring B] [inst_4 : Algeb
ra R₁ B] (f : A →ₐ[R₁] B) (r : R₁) (x : A ⧸ RingHom.ker f),   f.kerLift (r • x) 
= r • f.kerLift x
参数：f : A →ₐ[R₁] B；r : R₁；x : A ⧸ RingHom.ker f；r • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Quotient.mkₐ_surjective`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : 
CommSemiring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst
_3 : I.IsTwoSided],…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
theorem KerLift.map_smul (f : A →ₐ[R₁] B) (r : R₁) (x : A ⧸ (RingHom.ker f)) :
    f.kerLift (r • x) = r • f.kerLift x := by
  obtain ⟨a, rfl⟩ := Quotient.mkₐ_surjective R₁ _ x
  exact _root_.map_smul f _ _

/-- The induced algebras morphism from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotientKerAlgEquivOfRightInverse`) /
is surjective (`quotientKerAlgEquivOfSurjective`).
-/
/-
**Ideal.kerLiftAlg** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：kerLiftAlg (f : A ->ₐ[R₁] B) : A ⧸ (RingHom.ker f) ->ₐ[R₁] B
参数：f : A ->ₐ[R₁] B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.KerLift.map_smul`：∀ {R₁ : Type u_1} {A : Type u_3} {B : Type u_4} 
[inst : CommSemiring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A]   [inst_3 : S
emiring B] […

--- 原说明 ---
The induced algebras morphism from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotientKerAlgEquivOfRightIn
verse`) /
is surjective (`quotientKerAlgEquivOfSurjective`).
-/
def kerLiftAlg (f : A →ₐ[R₁] B) : A ⧸ (RingHom.ker f) →ₐ[R₁] B :=
  AlgHom.mk' (RingHom.kerLift (f : A →+* B)) fun _ _ => KerLift.map_smul f _ _

@[simp]
/-
**Ideal.kerLiftAlg_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：kerLiftAlg_mk (f : A ->ₐ[R₁] B) (a : A) : kerLiftAlg f (Quotient.mk (RingH
om.ker f) a) = f a
参数：f : A ->ₐ[R₁] B；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
-/
theorem kerLiftAlg_mk (f : A →ₐ[R₁] B) (a : A) :
    kerLiftAlg f (Quotient.mk (RingHom.ker f) a) = f a := by
  rfl

@[simp]
/-
**Ideal.kerLiftAlg_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：kerLiftAlg_toRingHom (f : A ->ₐ[R₁] B) : (kerLiftAlg f : A ⧸ ker f ->+* B)
 = RingHom.kerLift (f : A ->+* B)
参数：f : A ->ₐ[R₁] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
-/
theorem kerLiftAlg_toRingHom (f : A →ₐ[R₁] B) :
    (kerLiftAlg f : A ⧸ ker f →+* B) = RingHom.kerLift (f : A →+* B) :=
  rfl

/-- The induced algebra morphism from the quotient by the kernel is injective. -/
/-
**Ideal.kerLiftAlg_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：kerLiftAlg_injective (f : A ->ₐ[R₁] B) : Function.Injective (kerLiftAlg f)
参数：f : A ->ₐ[R₁] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.kerLift_injective`：kerLift_injective : Function.Injective (kerLi
ft f)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …

--- 原说明 ---
The induced algebra morphism from the quotient by the kernel is injective.
-/
theorem kerLiftAlg_injective (f : A →ₐ[R₁] B) : Function.Injective (kerLiftAlg f) :=
  RingHom.kerLift_injective (R := A) (S := B) f

/-- The **first isomorphism** theorem for algebras, computable version. -/
@[simps!]
/-
**Ideal.quotientKerAlgEquivOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientKerAlgEquivOfRightInverse {f : A ->ₐ[R₁] B} {g : B -> A} (hf : Fun
ction.RightInverse g f) : (A ⧸ RingHom.ker f) ≃ₐ[R₁] B
参数：hf : Function.RightInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **first isomorphism** theorem for algebras, computable version.
-/
def quotientKerAlgEquivOfRightInverse {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) : (A ⧸ RingHom.ker f) ≃ₐ[R₁] B :=
  { RingHom.quotientKerEquivOfRightInverse hf,
    kerLiftAlg f with }

/-- The **first isomorphism theorem** for algebras. -/
@[simps! -isSimp apply]
/-
**Ideal.quotientKerAlgEquivOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientKerAlgEquivOfSurjective {f : A ->ₐ[R₁] B} (hf : Function.Surjectiv
e f) : (A ⧸ (RingHom.ker f)) ≃ₐ[R₁] B
参数：hf : Function.Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **first isomorphism theorem** for algebras.
-/
noncomputable def quotientKerAlgEquivOfSurjective {f : A →ₐ[R₁] B} (hf : Function.Surjective f) :
    (A ⧸ (RingHom.ker f)) ≃ₐ[R₁] B :=
  quotientKerAlgEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)

@[simp]
/-
**Ideal.quotientKerAlgEquivOfSurjective_mk** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：quotientKerAlgEquivOfSurjective_mk {f : A ->ₐ[R₁] B} (hf : Function.Surjec
tive f) (a : A) : Ideal.quotientKerAlgEquivOfSurjective hf (Ideal.Quotient.mk _ 
a) = f a
参数：hf : Function.Surjective f；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
-/
lemma quotientKerAlgEquivOfSurjective_mk {f : A →ₐ[R₁] B} (hf : Function.Surjective f)
    (a : A) : Ideal.quotientKerAlgEquivOfSurjective hf (Ideal.Quotient.mk _ a) = f a :=
  rfl

@[simp]
/-
**Ideal.quotientKerAlgEquivOfSurjective_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Id
eal`。
形式化陈述：quotientKerAlgEquivOfSurjective_symm_apply {f : A ->ₐ[R₁] B} (hf : Functio
n.Surjective f) (a : A) : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f a) 
= a
参数：hf : Function.Surjective f；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma quotientKerAlgEquivOfSurjective_symm_apply {f : A →ₐ[R₁] B} (hf : Function.Surjective f)
    (a : A) : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f a) = a := by
  apply (Ideal.quotientKerAlgEquivOfSurjective hf).injective
  simp

section liftOfSurjective

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]

/-- `AlgHom` version of `RingHom.liftOfSurjective` that descends an algebra homomorphism
along a surjection. -/
noncomputable
/-
**Ideal._root_.AlgHom.liftOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.AlgHom.liftOfSurjective (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (g : A →ₐ[R] C) (H : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom) : B →ₐ[R] C :=
  .comp (Ideal.Quotient.liftₐ _ g H) (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Ideal._root_.AlgHom.liftOfSurjective_apply** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgHom.liftOfSurjective_apply (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (g : A →ₐ[R] C) (H : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom) (x) :
    AlgHom.liftOfSurjective f hf g H (f x) = g x := by
  dsimp [AlgHom.liftOfSurjective]
  erw [AlgEquiv.coe_toAlgHom] -- fixed after #21031
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
  rfl
/-
**Ideal._root_.AlgHom.liftOfSurjective_comp** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgHom.liftOfSurjective_comp (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (g : A →ₐ[R] C) (H : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom) :
    (AlgHom.liftOfSurjective f hf g H).comp f = g := by
  ext; simp
/-
**Ideal._root_.AlgHom.liftOfSurjective_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Ide
al`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgHom.liftOfSurjective_surjective (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (g : A →ₐ[R] C) (H : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom)
    (hg : Function.Surjective g) : Function.Surjective (AlgHom.liftOfSurjective f hf g H) :=
  .of_comp (g := f) (by convert! hg; ext; simp)

end liftOfSurjective

end

section Ring_Ring

variable {S : Type v} [Ring S]

/-- The ring hom `R/I →+* S/J` induced by a ring hom `f : R →+* S` with `I ≤ f⁻¹(J)` -/
/-
**Ideal.quotientMap** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientMap {I : Ideal R} (J : Ideal S) [I.IsTwoSided] [J.IsTwoSided] (f :
 R ->+* S) (hIJ : I <= J.comap f) : R ⧸ I ->+* S ⧸ J
参数：J : Ideal S；f : R ->+* S；hIJ : I <= J.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring hom `R/I →+* S/J` induced by a ring hom `f : R →+* S` with `I ≤ f⁻¹(J)`
-/
def quotientMap {I : Ideal R} (J : Ideal S) [I.IsTwoSided] [J.IsTwoSided] (f : R →+* S)
    (hIJ : I ≤ J.comap f) : R ⧸ I →+* S ⧸ J :=
  Quotient.lift I ((Quotient.mk J).comp f) fun _ ha => by
    simpa [Function.comp_apply, RingHom.coe_comp, Quotient.eq_zero_iff_mem] using hIJ ha

@[simp]
/-
**Ideal.quotientMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientMap_mk {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided] {
f : R ->+* S} {H : J <= I.comap f} {x : R} : quotientMap I f H (Quotient.mk J x)
 = Quotient.mk I (f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.lift_mk`：lift_mk (f : R ->+* S) (H : forall a : R, a in I
 -> f a = 0) : lift I f H (mk I a) = f a
-/
theorem quotientMap_mk {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : R →+* S} {H : J ≤ I.comap f} {x : R} :
    quotientMap I f H (Quotient.mk J x) = Quotient.mk I (f x) :=
  Quotient.lift_mk J _ _

@[simp]
/-
**Ideal.quotientMap_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientMap_algebraMap {J : Ideal A} {I : Ideal S} [I.IsTwoSided] [J.IsTwo
Sided] {f : A ->+* S} {H : J <= I.comap f} {x : R₁} : quotientMap I f H (algebra
Map R₁ (A ⧸ J) x) = Quotient.mk I (f (algebraMap _ _ x))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.lift_mk`：lift_mk (f : R ->+* S) (H : forall a : R, a in I
 -> f a = 0) : lift I f H (mk I a) = f a
-/
theorem quotientMap_algebraMap {J : Ideal A} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : A →+* S} {H : J ≤ I.comap f}
    {x : R₁} : quotientMap I f H (algebraMap R₁ (A ⧸ J) x) = Quotient.mk I (f (algebraMap _ _ x)) :=
  Quotient.lift_mk J _ _
/-
**Ideal.quotientMap_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientMap_comp_mk {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSid
ed] {f : R ->+* S} (H : J <= I.comap f) : (quotientMap I f H).comp (Quotient.mk 
J) = (Quotient.mk I).comp f
参数：H : J <= I.comap f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.quotientMap_mk`：quotientMap_mk {J : Ideal R} {I : Ideal S} [I.IsTw
oSided] [J.IsTwoSided] {f : R ->+* S} {H : J <= I.comap f} {x : R} : quotientMap
 I f H (Qu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem quotientMap_comp_mk {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : R →+* S} (H : J ≤ I.comap f) :
    (quotientMap I f H).comp (Quotient.mk J) = (Quotient.mk I).comp f :=
  RingHom.ext fun x => by simp only [Function.comp_apply, RingHom.coe_comp, Ideal.quotientMap_mk]

set_option backward.isDefEq.respectTransparency false in
/-
**Ideal.ker_quotientMap_mk** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：ker_quotientMap_mk {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided] : RingHom
.ker (quotientMap (J.map _) (Quotient.mk I) le_comap_map) = I.map (Quotient.mk J
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSidedMapRingHomOfRingHomSurjective`：∀ {R : Type u} {S : T
ype v} [inst : Semiring R] [inst_1 : Semiring S] (f : R →+* S) [RingHomSurjectiv
e f] (I : Ideal R)   [I.IsTwoSided], (I…
· 使用定理 `Ideal.Quotient.instRingHomSurjectiveQuotientMk`：∀ {R : Type u} [inst : R
ing R] {I : Ideal R} [inst_1 : I.IsTwoSided], RingHomSurjective (Ideal.Quotient.
mk I)
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.quotientMap.eq_1`：∀ {R : Type u} [inst : Ring R] {S : Type v} [ins
t_1 : Ring S] {I : Ideal R} (J : Ideal S) [inst_2 : I.IsTwoSided]   [inst_3 : J.
IsTwoSided] …
· 使用定理 `Ideal.ker_quotient_lift`：ker_quotient_lift {I : Ideal R} [I.IsTwoSided] 
(f : R ->+* S) (H : I <= ker f) : ker (Ideal.Quotient.lift I f H) = (RingHom.ker
 f).map (Quot…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comap_ker`：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).com
ap g = ker (f.comp g)
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Ideal.map_sup`：map_sup : (I ⊔ J).map f = I.map f ⊔ J.map f
· 使用定理 `Ideal.map_quotient_self`：map_quotient_self (I : Ideal R) [I.IsTwoSided] 
: map (Quotient.mk I) I = ⊥
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
-/
lemma ker_quotientMap_mk {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided] :
    RingHom.ker (quotientMap (J.map _) (Quotient.mk I) le_comap_map) = I.map (Quotient.mk J) := by
  rw [Ideal.quotientMap, Ideal.ker_quotient_lift, ← RingHom.comap_ker, Ideal.mk_ker,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]

section quotientEquiv

variable (I : Ideal R) (J : Ideal S) [I.IsTwoSided] [J.IsTwoSided]
    (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S))

/-- The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+* S`, where `J = f(I)`. -/
@[simps]
/-
**Ideal.quotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientEquiv : R ⧸ I ≃+* S ⧸ J where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+* S`, where `J = f
(I)`.
-/
def quotientEquiv : R ⧸ I ≃+* S ⧸ J where
  __ := quotientMap J f (hIJ ▸ le_comap_map)
  invFun := quotientMap I f.symm (hIJ ▸ (map_comap_of_equiv f).le)
  left_inv := by
    rintro ⟨r⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, RingHom.toFun_eq_coe,
      quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  right_inv := by
    rintro ⟨s⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, RingHom.toFun_eq_coe,
      quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]

-- Not `@[simp]` since `simp` proves it.
/-
**Ideal.quotientEquiv_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientEquiv_mk (x : R) : quotientEquiv I J f hIJ (Ideal.Quotient.mk I x)
 = Ideal.Quotient.mk J (f x)
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem quotientEquiv_mk (x : R) :
    quotientEquiv I J f hIJ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (f x) :=
  rfl

-- Not `@[simp]` since `simp` proves it.
/-
**Ideal.quotientEquiv_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientEquiv_symm_mk (x : S) : (quotientEquiv I J f hIJ).symm (Ideal.Quot
ient.mk J x) = Ideal.Quotient.mk I (f.symm x)
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem quotientEquiv_symm_mk (x : S) :
    (quotientEquiv I J f hIJ).symm (Ideal.Quotient.mk J x) = Ideal.Quotient.mk I (f.symm x) :=
  rfl

end quotientEquiv

/-- `H` and `h` are kept as separate hypothesis since H is used in constructing the quotient map. -/
/-
**Ideal.quotientMap_injective'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientMap_injective' {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwo
Sided] {f : R ->+* S} {H : J <= I.comap f} (h : I.comap f <= J) : Function.Injec
tive (quotientMap I f H)
参数：h : I.comap f <= J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.quotientMap_mk`：quotientMap_mk {J : Ideal R} {I : Ideal S} [I.IsTw
oSided] [J.IsTwoSided] {f : R ->+* S} {H : J <= I.comap f} {x : R} : quotientMap
 I f H (Qu…

--- 原说明 ---
`H` and `h` are kept as separate hypothesis since H is used in constructing the 
quotient map.
-/
theorem quotientMap_injective' {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : R →+* S} {H : J ≤ I.comap f} (h : I.comap f ≤ J) :
    Function.Injective (quotientMap I f H) := by
  refine (injective_iff_map_eq_zero (quotientMap I f H)).2 fun a ha => ?_
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective a
  rw [quotientMap_mk, Quotient.eq_zero_iff_mem] at ha
  exact Quotient.eq_zero_iff_mem.mpr (h ha)

/-- If we take `J = I.comap f` then `quotientMap` is injective automatically. -/
/-
**Ideal.quotientMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientMap_injective {I : Ideal S} {f : R ->+* S} [I.IsTwoSided] : Functi
on.Injective (quotientMap I f le_rfl)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.quotientMap_injective'`：quotientMap_injective' {J : Ideal R} {I : 
Ideal S} [I.IsTwoSided] [J.IsTwoSided] {f : R ->+* S} {H : J <= I.comap f} (h : 
I.comap f <= J) : …
· 使用定理 `Ideal.instIsTwoSidedComap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : 
Ideal S} [inst_…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
If we take `J = I.comap f` then `quotientMap` is injective automatically.
-/
theorem quotientMap_injective {I : Ideal S} {f : R →+* S} [I.IsTwoSided] :
    Function.Injective (quotientMap I f le_rfl) :=
  quotientMap_injective' le_rfl
/-
**Ideal.quotientMap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientMap_surjective {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwo
Sided] {f : R ->+* S} {H : J <= I.comap f} (hf : Function.Surjective f) : Functi
on.Surjective (quotientMap I f H)
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.quotientMap_mk`：quotientMap_mk {J : Ideal R} {I : Ideal S} [I.IsTw
oSided] [J.IsTwoSided] {f : R ->+* S} {H : J <= I.comap f} {x : R} : quotientMap
 I f H (Qu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem quotientMap_surjective {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : R →+* S} {H : J ≤ I.comap f}
    (hf : Function.Surjective f) : Function.Surjective (quotientMap I f H) := fun x =>
  let ⟨x, hx⟩ := Quotient.mk_surjective x
  let ⟨y, hy⟩ := hf x
  ⟨(Quotient.mk J) y, by simp [hx, hy]⟩

/-- Commutativity of a square is preserved when taking quotients by an ideal. -/
/-
**Ideal.comp_quotientMap_eq_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comp_quotientMap_eq_of_comp_eq {R' S' : Type*} [Ring R'] [Ring S'] {f : R 
->+* S} {f' : R' ->+* S'} {g : R ->+* R'} {g' : S ->+* S'} (hfg : f'.comp g = g'
.comp f) (I : Ideal S') [I.IsTwoSided] : let leq
参数：hfg : f'.comp g = g'.comp f；I : Ideal S'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Ideal.instIsTwoSidedComap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : 
Ideal S} [inst_…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.quotientMap_mk`：quotientMap_mk {J : Ideal R} {I : Ideal S} [I.IsTw
oSided] [J.IsTwoSided] {f : R ->+* S} {H : J <= I.comap f} {x : R} : quotientMap
 I f H (Qu…
· 使用定理 `RingHom.congr_arg`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} (f : α →+* β) {x_2 y : α},   x_2 = y → f x_2 = f 
y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)

--- 原说明 ---
Commutativity of a square is preserved when taking quotients by an ideal.
-/
theorem comp_quotientMap_eq_of_comp_eq {R' S' : Type*} [Ring R'] [Ring S'] {f : R →+* S}
    {f' : R' →+* S'} {g : R →+* R'} {g' : S →+* S'} (hfg : f'.comp g = g'.comp f)
    (I : Ideal S') [I.IsTwoSided] :
    let leq := le_of_eq (_root_.trans (comap_comap f g') (hfg ▸ comap_comap g f'))
    (quotientMap I g' le_rfl).comp (quotientMap (I.comap g') f le_rfl) =
    (quotientMap I f' le_rfl).comp (quotientMap (I.comap f') g leq) := by
  refine RingHom.ext fun a => ?_
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective a
  simp only [RingHom.comp_apply, quotientMap_mk]
  exact (Ideal.Quotient.mk I).congr_arg (_root_.trans (g'.comp_apply f r).symm
    (hfg ▸ f'.comp_apply g r))

end Ring_Ring


section

variable [Ring B] [Algebra R₁ B] {I : Ideal A} (J : Ideal B) [I.IsTwoSided] [J.IsTwoSided]

set_option backward.isDefEq.respectTransparency false in
/-- The algebra hom `A/I →+* B/J` induced by an algebra hom `f : A →ₐ[R₁] B` with `I ≤ f⁻¹(J)`. -/
/-
**Ideal.quotientMap** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientMap {I : Ideal R} (J : Ideal S) [I.IsTwoSided] [J.IsTwoSided] (f :
 R ->+* S) (hIJ : I <= J.comap f) : R ⧸ I ->+* S ⧸ J
参数：J : Ideal S；f : R ->+* S；hIJ : I <= J.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra hom `A/I →+* B/J` induced by an algebra hom `f : A →ₐ[R₁] B` with `I
 ≤ f⁻¹(J)`.
-/
def quotientMapₐ (f : A →ₐ[R₁] B) (hIJ : I ≤ J.comap f) :
    A ⧸ I →ₐ[R₁] B ⧸ J :=
  { quotientMap J (f : A →+* B) hIJ with commutes' := fun r => by simp only [RingHom.toFun_eq_coe,
    quotientMap_algebraMap, AlgHom.coe_toRingHom, AlgHom.commutes, Quotient.mk_algebraMap] }

@[simp]
/-
**Ideal.quotient_map_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotient_map_mkₐ (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) {x : A} :
    quotientMapₐ J f H (Quotient.mk I x) = Quotient.mkₐ R₁ J (f x) :=
  rfl
/-
**Ideal.quotient_map_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotient_map_comp_mkₐ (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) :
    (quotientMapₐ J f H).comp (Quotient.mkₐ R₁ I) = (Quotient.mkₐ R₁ J).comp f :=
  AlgHom.ext fun x => by simp only [quotient_map_mkₐ, Quotient.mkₐ_eq_mk, AlgHom.comp_apply]

set_option backward.isDefEq.respectTransparency false in
variable (I) in
/-- The algebra equiv `A/I ≃ₐ[R] B/J` induced by an algebra equiv `f : A ≃ₐ[R] B`,
where `J = f(I)`. -/
/-
**Ideal.quotientEquivAlg** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientEquivAlg (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A ->+* B)) : (A ⧸ 
I) ≃ₐ[R₁] B ⧸ J
参数：f : A ≃ₐ[R₁] B；hIJ : J = I.map (f : A ->+* B)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra equiv `A/I ≃ₐ[R] B/J` induced by an algebra equiv `f : A ≃ₐ[R] B`,
where `J = f(I)`.
-/
def quotientEquivAlg (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) :
    (A ⧸ I) ≃ₐ[R₁] B ⧸ J :=
  { quotientEquiv I J (f : A ≃+* B) hIJ with
    commutes' r := by simp }

@[simp]
/-
**Ideal.quotientEquivAlg_symm** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：quotientEquivAlg_symm (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A ->+* B)) : 
(quotientEquivAlg I J f hIJ).symm = quotientEquivAlg J I f.symm (by simp only [←
 AlgEquiv.toAlgHom_toRingHom, hIJ, map_map, ← AlgHom.comp_toRingHom, AlgEquiv.sy
mm_comp, AlgHom.id_toRingHom, map_id])
参数：f : A ≃ₐ[R₁] B；hIJ : J = I.map (f : A ->+* B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
lemma quotientEquivAlg_symm (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) :
    (quotientEquivAlg I J f hIJ).symm = quotientEquivAlg J I f.symm
      (by simp only [← AlgEquiv.toAlgHom_toRingHom, hIJ, map_map, ← AlgHom.comp_toRingHom,
        AlgEquiv.symm_comp, AlgHom.id_toRingHom, map_id]) :=
  rfl

@[simp]
/-
**Ideal.quotientEquivAlg_mk** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：quotientEquivAlg_mk (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A ->+* B)) (x :
 A) : Ideal.quotientEquivAlg I J f hIJ x = f x
参数：f : A ≃ₐ[R₁] B；hIJ : J = I.map (f : A ->+* B)；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
lemma quotientEquivAlg_mk (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) (x : A) :
    Ideal.quotientEquivAlg I J f hIJ x = f x :=
  rfl

end

/-- If `P` lies over `p`, then `R / p` has a canonical map to `A / P`. -/
/-
**Ideal.Quotient.algebraQuotientOfLEComap** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quoti
ent`。
形式化陈述：{A : Type u_3} →   [inst : Ring A] →     {R : Type u_5} →       [inst_1 : 
CommRing R] →         [inst_2 : Algebra R A] →           {p : Ideal R} →        
     {P : Ideal A} → [inst_3 : P.IsTwoSided] → p ≤ Ideal.comap (algebraMap R A) 
P → Algebra (R ⧸ p) (A ⧸ P)
参数：algebraMap R A；R ⧸ p；A ⧸ P。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
If `P` lies over `p`, then `R / p` has a canonical map to `A / P`.
-/
abbrev Quotient.algebraQuotientOfLEComap {R} [CommRing R] [Algebra R A] {p : Ideal R}
    {P : Ideal A} [P.IsTwoSided] (h : p ≤ comap (algebraMap R A) P) :
    Algebra (R ⧸ p) (A ⧸ P) where
  algebraMap := quotientMap P (algebraMap R A) h
  smul := Quotient.lift₂ (⟦· • ·⟧) fun r₁ a₁ r₂ a₂ hr ha ↦ Quotient.sound <| by
    have := h (p.quotientRel_def.mp hr)
    rw [mem_comap, map_sub] at this
    simpa only [Algebra.smul_def] using P.quotientRel_def.mpr
      (P.mul_sub_mul_mem this <| P.quotientRel_def.mp ha)
  smul_def' := by rintro ⟨_⟩ ⟨_⟩; exact congr_arg (⟦·⟧) (Algebra.smul_def _ _)
  commutes' := by rintro ⟨_⟩ ⟨_⟩; exact congr_arg (⟦·⟧) (Algebra.commutes _ _)
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) quotientAlgebra {R} [CommRing R] {I : Ideal A} [I.IsTwoSided]
    [Algebra R A] : Algebra (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) :=
  Quotient.algebraQuotientOfLEComap le_rfl
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R) {A} [CommRing R] [CommRing A] (I : Ideal A) [Algebra R A] :
    Algebra (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) := inferInstance
/-
**Ideal.algebraMap_quotient_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：algebraMap_quotient_injective {R} [CommRing R] {I : Ideal A} [I.IsTwoSided
] [Algebra R A] : Function.Injective (algebraMap (R ⧸ I.comap (algebraMap R A)) 
(A ⧸ I))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem algebraMap_quotient_injective {R} [CommRing R] {I : Ideal A} [I.IsTwoSided] [Algebra R A] :
    Function.Injective (algebraMap (R ⧸ I.comap (algebraMap R A)) (A ⧸ I)) := by
  rintro ⟨a⟩ ⟨b⟩ hab
  replace hab := Quotient.eq.mp hab
  rw [← map_sub] at hab
  exact Quotient.eq.mpr hab

variable (R₁)

/-- Quotienting by equal ideals gives equivalent algebras. -/
/-
**Ideal.quotientEquivAlgOfEq** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientEquivAlgOfEq {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I 
= J) : (A ⧸ I) ≃ₐ[R₁] A ⧸ J
参数：h : I = J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quotienting by equal ideals gives equivalent algebras.
-/
def quotientEquivAlgOfEq {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
    (A ⧸ I) ≃ₐ[R₁] A ⧸ J :=
  quotientEquivAlg I J AlgEquiv.refl <| h ▸ (map_id I).symm

@[simp]
/-
**Ideal.quotientEquivAlgOfEq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientEquivAlgOfEq_mk {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h :
 I = J) (x : A) : quotientEquivAlgOfEq R₁ h (Ideal.Quotient.mk I x) = Ideal.Quot
ient.mk J x
参数：h : I = J；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientEquivAlgOfEq_mk {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) (x : A) :
    quotientEquivAlgOfEq R₁ h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
  rfl

@[simp]
/-
**Ideal.quotientEquivAlgOfEq_coe_eq_factor** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientEquivAlgOfEq_coe_eq_factor {I J : Ideal A} [I.IsTwoSided] [J.IsTwo
Sided] (h : I = J) : (quotientEquivAlgOfEq R₁ h : A ⧸ I ->+* A ⧸ J) = Quotient.f
actor (le_of_eq h)
参数：h : I = J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem quotientEquivAlgOfEq_coe_eq_factorₐ
    {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
    (quotientEquivAlgOfEq R₁ h : A ⧸ I →ₐ[R₁] A ⧸ J) = Quotient.factorₐ R₁ (le_of_eq h) := rfl

@[simp]
/-
**Ideal.quotientEquivAlgOfEq_coe_eq_factor** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientEquivAlgOfEq_coe_eq_factor {I J : Ideal A} [I.IsTwoSided] [J.IsTwo
Sided] (h : I = J) : (quotientEquivAlgOfEq R₁ h : A ⧸ I ->+* A ⧸ J) = Quotient.f
actor (le_of_eq h)
参数：h : I = J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem quotientEquivAlgOfEq_coe_eq_factor
    {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
    (quotientEquivAlgOfEq R₁ h : A ⧸ I →+* A ⧸ J) = Quotient.factor (le_of_eq h) := rfl

@[simp]
/-
**Ideal.quotientEquivAlgOfEq_symm** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientEquivAlgOfEq_symm {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h
 : I = J) : (quotientEquivAlgOfEq R₁ h).symm = quotientEquivAlgOfEq R₁ h.symm
参数：h : I = J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem quotientEquivAlgOfEq_symm {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
    (quotientEquivAlgOfEq R₁ h).symm = quotientEquivAlgOfEq R₁ h.symm := by
  ext
  rfl

@[simp]
/-
**Ideal.comap_map_quotientMk** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：comap_map_quotientMk (I J : Ideal R) [I.IsTwoSided] : (J.map <| Ideal.Quot
ient.mk I).comap (Ideal.Quotient.mk I) = I ⊔ J
参数：I J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma comap_map_quotientMk (I J : Ideal R) [I.IsTwoSided] :
    (J.map <| Ideal.Quotient.mk I).comap (Ideal.Quotient.mk I) = I ⊔ J := by
  ext x
  simp only [mem_comap, mem_quotient_iff_mem_sup, sup_comm]
/-
**Ideal.comap_map_mk** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：comap_map_mk {I J : Ideal R} [I.IsTwoSided] (h : I <= J) : Ideal.comap (Id
eal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) J) = J
参数：h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.comap_map_quotientMk`：comap_map_quotientMk (I J : Ideal R) [I.IsTw
oSided] : (J.map <| Ideal.Quotient.mk I).comap (Ideal.Quotient.mk I) = I ⊔ J
-/
lemma comap_map_mk {I J : Ideal R} [I.IsTwoSided] (h : I ≤ J) :
    Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) J) = J := by
  simpa
/-
**Ideal.isPrime_map_quotientMk_of_isPrime** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：isPrime_map_quotientMk_of_isPrime {I : Ideal R} [I.IsTwoSided] {p : Ideal 
R} [p.IsPrime] (hIP : I <= p) : (p.map (Ideal.Quotient.mk I)).IsPrime
参数：hIP : I <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_isPrime_of_surjective`：map_isPrime_of_surjective {f : F} (hf :
 Function.Surjective f) {I : Ideal R} [H : IsPrime I] (hk : RingHom.ker f <= I) 
: IsPrime (map f I)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
-/
lemma isPrime_map_quotientMk_of_isPrime {I : Ideal R} [I.IsTwoSided] {p : Ideal R}
    [p.IsPrime] (hIP : I ≤ p) : (p.map (Ideal.Quotient.mk I)).IsPrime := by
  apply Ideal.map_isPrime_of_surjective
  · exact Quotient.mk_surjective
  · simpa

/-- The **first isomorphism theorem** for commutative algebras (`AlgHom.range` version). -/
/-
**Ideal.quotientKerEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientKerEquivRange {R A B : Type*} [CommSemiring R] [Ring A] [Algebra R
 A] [Semiring B] [Algebra R B] (f : A ->ₐ[R] B) : (A ⧸ RingHom.ker f) ≃ₐ[R] f.ra
nge
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **first isomorphism theorem** for commutative algebras (`AlgHom.range` versi
on).
-/
noncomputable def quotientKerEquivRange
    {R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Semiring B] [Algebra R B]
    (f : A →ₐ[R] B) :
    (A ⧸ RingHom.ker f) ≃ₐ[R] f.range :=
  (Ideal.quotientEquivAlgOfEq R (AlgHom.ker_rangeRestrict f).symm).trans <|
    Ideal.quotientKerAlgEquivOfSurjective f.rangeRestrict_surjective

end QuotientAlgebra

end Ideal

section quotientBot

variable {R S : Type*}

variable (R) in
/-- The quotient of a ring by he zero ideal is isomorphic to the ring itself. -/
/-
**RingEquiv.quotientBot** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingEquiv.quotientBot [Ring R] : R ⧸ (⊥ : Ideal R) ≃+* R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient of a ring by he zero ideal is isomorphic to the ring itself.
-/
def RingEquiv.quotientBot [Ring R] : R ⧸ (⊥ : Ideal R) ≃+* R :=
  (Ideal.quotEquivOfEq (RingHom.ker_coe_equiv <| .refl _).symm).trans <|
    RingHom.quotientKerEquivOfRightInverse (f := .id R) (g := _root_.id) fun _ ↦ rfl

@[simp]
/-
**RingEquiv.quotientBot_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingEquiv.quotientBot_mk [Ring R] (r : R) : RingEquiv.quotientBot R (Ideal
.Quotient.mk ⊥ r) = r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSidedBot`：∀ {α : Type u} [inst : Semiring α], ⊥.IsTwoSide
d
-/
lemma RingEquiv.quotientBot_mk [Ring R] (r : R) :
    RingEquiv.quotientBot R (Ideal.Quotient.mk ⊥ r) = r :=
  rfl

@[simp]
/-
**RingEquiv.quotientBot_symm_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingEquiv.quotientBot_symm_mk [Ring R] (r : R) : (RingEquiv.quotientBot R)
.symm r = r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSidedBot`：∀ {α : Type u} [inst : Semiring α], ⊥.IsTwoSide
d
-/
lemma RingEquiv.quotientBot_symm_mk [Ring R] (r : R) :
    (RingEquiv.quotientBot R).symm r = r :=
  rfl

variable (R S) in
/-- `RingEquiv.quotientBot` as an algebra isomorphism. -/
/-
**AlgEquiv.quotientBot** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgEquiv.quotientBot [CommSemiring R] [Ring S] [Algebra R S] : (S ⧸ (⊥ : I
deal S)) ≃ₐ[R] S where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RingEquiv.quotientBot` as an algebra isomorphism.
-/
def AlgEquiv.quotientBot [CommSemiring R] [Ring S] [Algebra R S] :
    (S ⧸ (⊥ : Ideal S)) ≃ₐ[R] S where
  __ := RingEquiv.quotientBot S
  commutes' x := by simp [← Ideal.Quotient.mk_algebraMap]

@[simp]
/-
**AlgEquiv.quotientBot_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgEquiv.quotientBot_mk [CommSemiring R] [CommRing S] [Algebra R S] (s : S
) : AlgEquiv.quotientBot R S (Ideal.Quotient.mk ⊥ s) = s
参数：s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSidedBot`：∀ {α : Type u} [inst : Semiring α], ⊥.IsTwoSide
d
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma AlgEquiv.quotientBot_mk [CommSemiring R] [CommRing S] [Algebra R S] (s : S) :
    AlgEquiv.quotientBot R S (Ideal.Quotient.mk ⊥ s) = s :=
  rfl

@[simp]
/-
**AlgEquiv.quotientBot_symm_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgEquiv.quotientBot_symm_mk [CommSemiring R] [CommRing S] [Algebra R S] (
s : S) : (AlgEquiv.quotientBot R S).symm s = s
参数：s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSidedBot`：∀ {α : Type u} [inst : Semiring α], ⊥.IsTwoSide
d
-/
lemma AlgEquiv.quotientBot_symm_mk [CommSemiring R] [CommRing S] [Algebra R S]
    (s : S) : (AlgEquiv.quotientBot R S).symm s = s :=
  rfl

end quotientBot

namespace DoubleQuot

open Ideal

variable {R : Type u}

section

variable [CommRing R] (I J : Ideal R)

/-- The obvious ring hom `R/I → R/(I ⊔ J)` -/
/-
**DoubleQuot.quotLeftToQuotSup** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotLeftToQuotSup : R ⧸ I ->+* R ⧸ I ⊔ J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The obvious ring hom `R/I → R/(I ⊔ J)`
-/
def quotLeftToQuotSup : R ⧸ I →+* R ⧸ I ⊔ J :=
  Ideal.Quotient.factor le_sup_left

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of `quotLeftToQuotSup` -/
/-
**DoubleQuot.ker_quotLeftToQuotSup** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
形式化陈述：ker_quotLeftToQuotSup : RingHom.ker (quotLeftToQuotSup I J) = J.map (Ideal
.Quotient.mk I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ker_quotient_lift`：ker_quotient_lift {I : Ideal R} [I.IsTwoSided] 
(f : R ->+* S) (H : I <= ker f) : ker (Ideal.Quotient.lift I f H) = (RingHom.ker
 f).map (Quot…
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Ideal.map_eq_iff_sup_ker_eq_of_surjective`：map_eq_iff_sup_ker_eq_of_surj
ective {I J : Ideal R} (f : R ->+* S) (hf : Function.Surjective f) : map f I = m
ap f J ↔ I ⊔ RingHom.ker f = J …
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The kernel of `quotLeftToQuotSup`
-/
theorem ker_quotLeftToQuotSup : RingHom.ker (quotLeftToQuotSup I J) =
    J.map (Ideal.Quotient.mk I) := by
  simp only [mk_ker, sup_idem, sup_comm, quotLeftToQuotSup, Quotient.factor, ker_quotient_lift,
    map_eq_iff_sup_ker_eq_of_surjective (Ideal.Quotient.mk I) Quotient.mk_surjective, ← sup_assoc]

/-- The ring homomorphism `(R/I)/J' -> R/(I ⊔ J)` induced by `quotLeftToQuotSup` where `J'`
  is the image of `J` in `R/I` -/
/-
**DoubleQuot.quotQuotToQuotSup** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotToQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ->+* R ⧸ I ⊔ J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The ring homomorphism `(R/I)/J' -> R/(I ⊔ J)` induced by `quotLeftToQuotSup` whe
re `J'`
  is the image of `J` in `R/I`
-/
def quotQuotToQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) →+* R ⧸ I ⊔ J :=
  Ideal.Quotient.lift (J.map (Ideal.Quotient.mk I)) (quotLeftToQuotSup I J)
    (ker_quotLeftToQuotSup I J).symm.le

/-- The composite of the maps `R → (R/I)` and `(R/I) → (R/I)/J'` -/
/-
**DoubleQuot.quotQuotMk** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotMk : R ->+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The composite of the maps `R → (R/I)` and `(R/I) → (R/I)/J'`
-/
def quotQuotMk : R →+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  (Ideal.Quotient.mk (J.map (Ideal.Quotient.mk I))).comp (Ideal.Quotient.mk I)

/-- The kernel of `quotQuotMk` -/
/-
**DoubleQuot.ker_quotQuotMk** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
形式化陈述：ker_quotQuotMk : RingHom.ker (quotQuotMk I J) = I ⊔ J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `DoubleQuot.quotQuotMk.eq_1`：∀ {R : Type u} [inst : CommRing R] (I J : Id
eal R),   DoubleQuot.quotQuotMk I J = (Ideal.Quotient.mk (Ideal.map (Ideal.Quoti
ent.mk I) J)).co…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `RingHom.ker.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Sem
iring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F 
R S] (…
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a

--- 原说明 ---
The kernel of `quotQuotMk`
-/
theorem ker_quotQuotMk : RingHom.ker (quotQuotMk I J) = I ⊔ J := by
  rw [RingHom.ker_eq_comap_bot, quotQuotMk, ← comap_comap, ← RingHom.ker, mk_ker,
    comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, ← RingHom.ker,
    mk_ker, sup_comm]

/-- The ring homomorphism `R/(I ⊔ J) → (R/I)/J'` induced by `quotQuotMk` -/
/-
**DoubleQuot.liftSupQuotQuotMk** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：liftSupQuotQuotMk (I J : Ideal R) : R ⧸ I ⊔ J ->+* (R ⧸ I) ⧸ J.map (Ideal.
Quotient.mk I)
参数：I J : Ideal R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The ring homomorphism `R/(I ⊔ J) → (R/I)/J'` induced by `quotQuotMk`
-/
def liftSupQuotQuotMk (I J : Ideal R) : R ⧸ I ⊔ J →+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  Ideal.Quotient.lift (I ⊔ J) (quotQuotMk I J) (ker_quotQuotMk I J).symm.le

/-- `quotQuotToQuotSup` and `liftSupQuotQuotMk` are inverse isomorphisms. In the case where
`I ≤ J`, this is the Third Isomorphism Theorem (see `quotQuotEquivQuotOfLe`). -/
/-
**DoubleQuot.quotQuotEquivQuotSup** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I ⊔ J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
`quotQuotToQuotSup` and `liftSupQuotQuotMk` are inverse isomorphisms. In the cas
e where
`I ≤ J`, this is the Third Isomorphism Theorem (see `quotQuotEquivQuotOfLe`).
-/
def quotQuotEquivQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I ⊔ J :=
  RingEquiv.ofRingHom (quotQuotToQuotSup I J) (liftSupQuotQuotMk I J)
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      rfl)
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      rfl)

@[simp]
/-
**DoubleQuot.quotQuotEquivQuotSup_quotQuotMk** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQu
ot`。
形式化陈述：quotQuotEquivQuotSup_quotQuotMk (x : R) : quotQuotEquivQuotSup I J (quotQu
otMk I J x) = Ideal.Quotient.mk (I ⊔ J) x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivQuotSup_quotQuotMk (x : R) :
    quotQuotEquivQuotSup I J (quotQuotMk I J x) = Ideal.Quotient.mk (I ⊔ J) x :=
  rfl

@[simp]
/-
**DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk** 是 Mathlib 中的一个定理，位于命名空间 `Dou
bleQuot`。
形式化陈述：quotQuotEquivQuotSup_symm_quotQuotMk (x : R) : (quotQuotEquivQuotSup I J).
symm (Ideal.Quotient.mk (I ⊔ J) x) = quotQuotMk I J x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivQuotSup_symm_quotQuotMk (x : R) :
    (quotQuotEquivQuotSup I J).symm (Ideal.Quotient.mk (I ⊔ J) x) = quotQuotMk I J x :=
  rfl

/-- The obvious isomorphism `(R/I)/J' → (R/J)/I'` -/
/-
**DoubleQuot.quotQuotEquivComm** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivComm : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* (R ⧸ J) ⧸ I.
map (Ideal.Quotient.mk J)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The obvious isomorphism `(R/I)/J' → (R/J)/I'`
-/
def quotQuotEquivComm : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+*
    (R ⧸ J) ⧸ I.map (Ideal.Quotient.mk J) :=
  ((quotQuotEquivQuotSup I J).trans (quotEquivOfEq (sup_comm ..))).trans
    (quotQuotEquivQuotSup J I).symm

@[simp]
/-
**DoubleQuot.quotQuotEquivComm_quotQuotMk** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`
。
形式化陈述：quotQuotEquivComm_quotQuotMk (x : R) : quotQuotEquivComm I J (quotQuotMk I
 J x) = quotQuotMk J I x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivComm_quotQuotMk (x : R) :
    quotQuotEquivComm I J (quotQuotMk I J x) = quotQuotMk J I x :=
  rfl

@[simp]
/-
**DoubleQuot.quotQuotEquivComm_comp_quotQuotMk** 是 Mathlib 中的一个定理，位于命名空间 `Double
Quot`。
形式化陈述：quotQuotEquivComm_comp_quotQuotMk : RingHom.comp (↑(quotQuotEquivComm I J)
) (quotQuotMk I J) = quotQuotMk J I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `DoubleQuot.quotQuotEquivComm_quotQuotMk`：quotQuotEquivComm_quotQuotMk (x
 : R) : quotQuotEquivComm I J (quotQuotMk I J x) = quotQuotMk J I x
-/
theorem quotQuotEquivComm_comp_quotQuotMk :
    RingHom.comp (↑(quotQuotEquivComm I J)) (quotQuotMk I J) = quotQuotMk J I :=
  RingHom.ext <| quotQuotEquivComm_quotQuotMk I J

@[simp]
/-
**DoubleQuot.quotQuotEquivComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivComm_symm : (quotQuotEquivComm I J).symm = quotQuotEquivComm 
J I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivComm_symm : (quotQuotEquivComm I J).symm = quotQuotEquivComm J I := by
  rfl

variable {I J}

/-- **The Third Isomorphism theorem** for rings. See `quotQuotEquivQuotSup` for a version
    that does not assume an inclusion of ideals. -/
/-
**DoubleQuot.quotQuotEquivQuotOfLE** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivQuotOfLE (h : I <= J) : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)
 ≃+* R ⧸ J
参数：h : I <= J。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
**The Third Isomorphism theorem** for rings. See `quotQuotEquivQuotSup` for a ve
rsion
    that does not assume an inclusion of ideals.
-/
def quotQuotEquivQuotOfLE (h : I ≤ J) : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ J :=
  (quotQuotEquivQuotSup I J).trans (Ideal.quotEquivOfEq <| sup_eq_right.mpr h)

@[simp]
/-
**DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQ
uot`。
形式化陈述：quotQuotEquivQuotOfLE_quotQuotMk (x : R) (h : I <= J) : quotQuotEquivQuotO
fLE h (quotQuotMk I J x) = (Ideal.Quotient.mk J) x
参数：x : R；h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivQuotOfLE_quotQuotMk (x : R) (h : I ≤ J) :
    quotQuotEquivQuotOfLE h (quotQuotMk I J x) = (Ideal.Quotient.mk J) x :=
  rfl

@[simp]
/-
**DoubleQuot.quotQuotEquivQuotOfLE_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot
`。
形式化陈述：quotQuotEquivQuotOfLE_symm_mk (x : R) (h : I <= J) : (quotQuotEquivQuotOfL
E h).symm ((Ideal.Quotient.mk J) x) = quotQuotMk I J x
参数：x : R；h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivQuotOfLE_symm_mk (x : R) (h : I ≤ J) :
    (quotQuotEquivQuotOfLE h).symm ((Ideal.Quotient.mk J) x) = quotQuotMk I J x :=
  rfl
/-
**DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMk** 是 Mathlib 中的一个定理，位于命名空间 `Do
ubleQuot`。
形式化陈述：quotQuotEquivQuotOfLE_comp_quotQuotMk (h : I <= J) : RingHom.comp (↑(quotQ
uotEquivQuotOfLE h)) (quotQuotMk I J) = (Ideal.Quotient.mk J)
参数：h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem quotQuotEquivQuotOfLE_comp_quotQuotMk (h : I ≤ J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLE h)) (quotQuotMk I J) = (Ideal.Quotient.mk J) := by
  ext
  rfl
/-
**DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `Doubl
eQuot`。
形式化陈述：quotQuotEquivQuotOfLE_symm_comp_mk (h : I <= J) : RingHom.comp (↑(quotQuot
EquivQuotOfLE h).symm) (Ideal.Quotient.mk J) = quotQuotMk I J
参数：h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem quotQuotEquivQuotOfLE_symm_comp_mk (h : I ≤ J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLE h).symm) (Ideal.Quotient.mk J) = quotQuotMk I J := by
  ext
  rfl

end

section Algebra

@[simp]
/-
**DoubleQuot.quotQuotEquivComm_mk_mk** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivComm_mk_mk [CommRing R] (I J : Ideal R) (x : R) : quotQuotEqu
ivComm I J (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) = algebraMap R _ x
参数：I J : Ideal R；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivComm_mk_mk [CommRing R] (I J : Ideal R) (x : R) :
    quotQuotEquivComm I J (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) = algebraMap R _ x :=
  rfl

variable [CommSemiring R] {A : Type v} [CommRing A] [Algebra R A] (I J : Ideal A)

@[simp]
/-
**DoubleQuot.quotQuotEquivQuotSup_quot_quot_algebraMap** 是 Mathlib 中的一个定理，位于命名空间
 `DoubleQuot`。
形式化陈述：quotQuotEquivQuotSup_quot_quot_algebraMap (x : R) : DoubleQuot.quotQuotEqu
ivQuotSup I J (algebraMap R _ x) = algebraMap _ _ x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivQuotSup_quot_quot_algebraMap (x : R) :
    DoubleQuot.quotQuotEquivQuotSup I J (algebraMap R _ x) = algebraMap _ _ x :=
  rfl

@[simp]
/-
**DoubleQuot.quotQuotEquivComm_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`
。
形式化陈述：quotQuotEquivComm_algebraMap (x : R) : quotQuotEquivComm I J (algebraMap R
 _ x) = algebraMap _ _ x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivComm_algebraMap (x : R) :
    quotQuotEquivComm I J (algebraMap R _ x) = algebraMap _ _ x :=
  rfl

end Algebra

section AlgebraQuotient

variable (R) {A : Type*} [CommSemiring R] [CommRing A] [Algebra R A] (I J : Ideal A)

/-- The natural algebra homomorphism `A / I → A / (I ⊔ J)`. -/
/-
**DoubleQuot.quotLeftToQuotSup** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotLeftToQuotSup : R ⧸ I ->+* R ⧸ I ⊔ J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The natural algebra homomorphism `A / I → A / (I ⊔ J)`.
-/
def quotLeftToQuotSupₐ : A ⧸ I →ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotLeftToQuotSup I J) fun _ => rfl

@[simp]
/-
**DoubleQuot.quotLeftToQuotSup** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotLeftToQuotSup : R ⧸ I ->+* R ⧸ I ⊔ J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotLeftToQuotSupₐ_toRingHom :
    (quotLeftToQuotSupₐ R I J : _ →+* _) = quotLeftToQuotSup I J :=
  rfl

@[simp]
/-
**DoubleQuot.coe_quotLeftToQuotSup** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_quotLeftToQuotSupₐ : ⇑(quotLeftToQuotSupₐ R I J) = quotLeftToQuotSup I J :=
  rfl

/-- The algebra homomorphism `(A / I) / J' -> A / (I ⊔ J)` induced by `quotQuotToQuotSup`,
  where `J'` is the projection of `J` in `A / I`. -/
/-
**DoubleQuot.quotQuotToQuotSup** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotToQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ->+* R ⧸ I ⊔ J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The algebra homomorphism `(A / I) / J' -> A / (I ⊔ J)` induced by `quotQuotToQuo
tSup`,
  where `J'` is the projection of `J` in `A / I`.
-/
def quotQuotToQuotSupₐ : (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) →ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotQuotToQuotSup I J) fun _ => rfl

@[simp]
/-
**DoubleQuot.quotQuotToQuotSup** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotToQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ->+* R ⧸ I ⊔ J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotToQuotSupₐ_toRingHom :
    ((quotQuotToQuotSupₐ R I J) : _ ⧸ map (Ideal.Quotient.mkₐ R I) J →+* _) =
      quotQuotToQuotSup I J :=
  rfl

@[simp]
/-
**DoubleQuot.coe_quotQuotToQuotSup** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_quotQuotToQuotSupₐ : ⇑(quotQuotToQuotSupₐ R I J) = quotQuotToQuotSup I J :=
  rfl

/-- The composition of the algebra homomorphisms `A → (A / I)` and `(A / I) → (A / I) / J'`,
  where `J'` is the projection `J` in `A / I`. -/
/-
**DoubleQuot.quotQuotMk** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotMk : R ->+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The composition of the algebra homomorphisms `A → (A / I)` and `(A / I) → (A / I
) / J'`,
  where `J'` is the projection `J` in `A / I`.
-/
def quotQuotMkₐ : A →ₐ[R] (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) :=
  AlgHom.mk (quotQuotMk I J) fun _ => rfl

@[simp]
/-
**DoubleQuot.quotQuotMk** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotMk : R ->+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotMkₐ_toRingHom :
    (quotQuotMkₐ R I J : _ →+* _ ⧸ J.map (Quotient.mkₐ R I)) = quotQuotMk I J :=
  rfl

@[simp]
/-
**DoubleQuot.coe_quotQuotMk** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_quotQuotMkₐ : ⇑(quotQuotMkₐ R I J) = quotQuotMk I J :=
  rfl

/-- The injective algebra homomorphism `A / (I ⊔ J) → (A / I) / J'` induced by `quotQuotMk`,
  where `J'` is the projection `J` in `A / I`. -/
/-
**DoubleQuot.liftSupQuotQuotMk** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：liftSupQuotQuotMk (I J : Ideal R) : R ⧸ I ⊔ J ->+* (R ⧸ I) ⧸ J.map (Ideal.
Quotient.mk I)
参数：I J : Ideal R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The injective algebra homomorphism `A / (I ⊔ J) → (A / I) / J'` induced by `quot
QuotMk`,
  where `J'` is the projection `J` in `A / I`.
-/
def liftSupQuotQuotMkₐ (I J : Ideal A) : A ⧸ I ⊔ J →ₐ[R] (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) :=
  AlgHom.mk (liftSupQuotQuotMk I J) fun _ => rfl

@[simp]
/-
**DoubleQuot.liftSupQuotQuotMk** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：liftSupQuotQuotMk (I J : Ideal R) : R ⧸ I ⊔ J ->+* (R ⧸ I) ⧸ J.map (Ideal.
Quotient.mk I)
参数：I J : Ideal R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem liftSupQuotQuotMkₐ_toRingHom :
    (liftSupQuotQuotMkₐ R I J : _ →+* _ ⧸ J.map (Quotient.mkₐ R I)) = liftSupQuotQuotMk I J :=
  rfl

@[simp]
/-
**DoubleQuot.coe_liftSupQuotQuotMk** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_liftSupQuotQuotMkₐ : ⇑(liftSupQuotQuotMkₐ R I J) = liftSupQuotQuotMk I J :=
  rfl

/-- `quotQuotToQuotSup` and `liftSupQuotQuotMk` are inverse isomorphisms. In the case where
`I ≤ J`, this is the Third Isomorphism Theorem (see `DoubleQuot.quotQuotEquivQuotOfLE`). -/
/-
**DoubleQuot.quotQuotEquivQuotSup** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I ⊔ J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
`quotQuotToQuotSup` and `liftSupQuotQuotMk` are inverse isomorphisms. In the cas
e where
`I ≤ J`, this is the Third Isomorphism Theorem (see `DoubleQuot.quotQuotEquivQuo
tOfLE`).
-/
def quotQuotEquivQuotSupₐ : ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] A ⧸ I ⊔ J :=
  AlgEquiv.ofRingEquiv (f := quotQuotEquivQuotSup I J) fun _ => rfl

@[simp]
/-
**DoubleQuot.quotQuotEquivQuotSup** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I ⊔ J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivQuotSupₐ_toRingEquiv :
    (quotQuotEquivQuotSupₐ R I J : _ ⧸ J.map (Quotient.mkₐ R I) ≃+* _) = quotQuotEquivQuotSup I J :=
  rfl

@[simp]
/-
**DoubleQuot.coe_quotQuotEquivQuotSup** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_quotQuotEquivQuotSupₐ : ⇑(quotQuotEquivQuotSupₐ R I J) = quotQuotEquivQuotSup I J :=
  rfl

@[simp]
/-
**DoubleQuot.quotQuotEquivQuotSup** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I ⊔ J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivQuotSupₐ_symm_toRingEquiv :
    ((quotQuotEquivQuotSupₐ R I J).symm : _ ≃+* _ ⧸ J.map (Quotient.mkₐ R I)) =
      (quotQuotEquivQuotSup I J).symm :=
  rfl

@[simp]
/-
**DoubleQuot.coe_quotQuotEquivQuotSup** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_quotQuotEquivQuotSupₐ_symm :
    ⇑(quotQuotEquivQuotSupₐ R I J).symm = (quotQuotEquivQuotSup I J).symm :=
  rfl

/-- The natural algebra isomorphism `(A / I) / J' → (A / J) / I'`,
  where `J'` (resp. `I'`) is the projection of `J` in `A / I` (resp. `I` in `A / J`). -/
/-
**DoubleQuot.quotQuotEquivComm** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivComm : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* (R ⧸ J) ⧸ I.
map (Ideal.Quotient.mk J)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The natural algebra isomorphism `(A / I) / J' → (A / J) / I'`,
  where `J'` (resp. `I'`) is the projection of `J` in `A / I` (resp. `I` in `A /
 J`).
-/
def quotQuotEquivCommₐ :
    ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] (A ⧸ J) ⧸ I.map (Quotient.mkₐ R J) :=
  AlgEquiv.ofRingEquiv (f := quotQuotEquivComm I J) fun _ => rfl

@[simp]
/-
**DoubleQuot.quotQuotEquivComm** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivComm : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* (R ⧸ J) ⧸ I.
map (Ideal.Quotient.mk J)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivCommₐ_toRingEquiv :
    (quotQuotEquivCommₐ R I J : _ ⧸ J.map (Quotient.mkₐ R I) ≃+* _ ⧸ I.map (Quotient.mkₐ R J)) =
      quotQuotEquivComm I J :=
  rfl

@[simp]
/-
**DoubleQuot.coe_quotQuotEquivComm** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_quotQuotEquivCommₐ : ⇑(quotQuotEquivCommₐ R I J) = ⇑(quotQuotEquivComm I J) :=
  rfl

@[simp]
/-
**DoubleQuot.quotQuotEquivComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivComm_symm : (quotQuotEquivComm I J).symm = quotQuotEquivComm 
J I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivComm_symmₐ : (quotQuotEquivCommₐ R I J).symm = quotQuotEquivCommₐ R J I := by
  rfl

@[simp]
/-
**DoubleQuot.quotQuotEquivComm_comp_quotQuotMk** 是 Mathlib 中的一个定理，位于命名空间 `Double
Quot`。
形式化陈述：quotQuotEquivComm_comp_quotQuotMk : RingHom.comp (↑(quotQuotEquivComm I J)
) (quotQuotMk I J) = quotQuotMk J I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `DoubleQuot.quotQuotEquivComm_quotQuotMk`：quotQuotEquivComm_quotQuotMk (x
 : R) : quotQuotEquivComm I J (quotQuotMk I J x) = quotQuotMk J I x
-/
theorem quotQuotEquivComm_comp_quotQuotMkₐ :
    AlgHom.comp (↑(quotQuotEquivCommₐ R I J)) (quotQuotMkₐ R I J) = quotQuotMkₐ R J I :=
  AlgHom.ext <| quotQuotEquivComm_quotQuotMk I J

variable {I J}

/-- The **third isomorphism theorem** for algebras. See `quotQuotEquivQuotSupₐ` for version
    that does not assume an inclusion of ideals. -/
/-
**DoubleQuot.quotQuotEquivQuotOfLE** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivQuotOfLE (h : I <= J) : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)
 ≃+* R ⧸ J
参数：h : I <= J。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The **third isomorphism theorem** for algebras. See `quotQuotEquivQuotSupₐ` for 
version
    that does not assume an inclusion of ideals.
-/
def quotQuotEquivQuotOfLEₐ (h : I ≤ J) : ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] A ⧸ J :=
  AlgEquiv.ofRingEquiv (f := quotQuotEquivQuotOfLE h) fun _ => rfl

@[simp]
/-
**DoubleQuot.quotQuotEquivQuotOfLE** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivQuotOfLE (h : I <= J) : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)
 ≃+* R ⧸ J
参数：h : I <= J。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivQuotOfLEₐ_toRingEquiv (h : I ≤ J) :
    (quotQuotEquivQuotOfLEₐ R h : _ ⧸ J.map (Quotient.mkₐ R I) ≃+* _) = quotQuotEquivQuotOfLE h :=
  rfl

@[simp]
/-
**DoubleQuot.coe_quotQuotEquivQuotOfLE** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_quotQuotEquivQuotOfLEₐ (h : I ≤ J) :
    ⇑(quotQuotEquivQuotOfLEₐ R h) = quotQuotEquivQuotOfLE h :=
  rfl

@[simp]
/-
**DoubleQuot.quotQuotEquivQuotOfLE** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivQuotOfLE (h : I <= J) : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)
 ≃+* R ⧸ J
参数：h : I <= J。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotQuotEquivQuotOfLEₐ_symm_toRingEquiv (h : I ≤ J) :
    ((quotQuotEquivQuotOfLEₐ R h).symm : _ ≃+* _ ⧸ J.map (Quotient.mkₐ R I)) =
      (quotQuotEquivQuotOfLE h).symm :=
  rfl

@[simp]
/-
**DoubleQuot.coe_quotQuotEquivQuotOfLE** 是 Mathlib 中的一个定理，位于命名空间 `DoubleQuot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_quotQuotEquivQuotOfLEₐ_symm (h : I ≤ J) :
    ⇑(quotQuotEquivQuotOfLEₐ R h).symm = (quotQuotEquivQuotOfLE h).symm :=
  rfl

@[simp]
/-
**DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMk** 是 Mathlib 中的一个定理，位于命名空间 `Do
ubleQuot`。
形式化陈述：quotQuotEquivQuotOfLE_comp_quotQuotMk (h : I <= J) : RingHom.comp (↑(quotQ
uotEquivQuotOfLE h)) (quotQuotMk I J) = (Ideal.Quotient.mk J)
参数：h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem quotQuotEquivQuotOfLE_comp_quotQuotMkₐ (h : I ≤ J) :
    AlgHom.comp (↑(quotQuotEquivQuotOfLEₐ R h)) (quotQuotMkₐ R I J) = Quotient.mkₐ R J :=
  rfl

@[simp]
/-
**DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `Doubl
eQuot`。
形式化陈述：quotQuotEquivQuotOfLE_symm_comp_mk (h : I <= J) : RingHom.comp (↑(quotQuot
EquivQuotOfLE h).symm) (Ideal.Quotient.mk J) = quotQuotMk I J
参数：h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem quotQuotEquivQuotOfLE_symm_comp_mkₐ (h : I ≤ J) :
    AlgHom.comp (↑(quotQuotEquivQuotOfLEₐ R h).symm) (Quotient.mkₐ R J) = quotQuotMkₐ R I J :=
  rfl
/-
**DoubleQuot.quotQuotEquivQuotOfLE** 是 Mathlib 中的一个定义，位于命名空间 `DoubleQuot`。
形式化陈述：quotQuotEquivQuotOfLE (h : I <= J) : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)
 ≃+* R ⧸ J
参数：h : I <= J。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma quotQuotEquivQuotOfLEₐ_comp_mkₐ (h : I ≤ J) :
    (quotQuotEquivQuotOfLEₐ R h).toAlgHom.comp (Ideal.Quotient.mkₐ _ _) =
      Ideal.Quotient.factorₐ _ h := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end AlgebraQuotient
end DoubleQuot

namespace Ideal

section PowQuot

variable {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)

set_option backward.isDefEq.respectTransparency false in
/-- `I ^ n ⧸ I ^ (n + 1)` can be viewed as a quotient module and as ideal of `R ⧸ I ^ (n + 1)`.
This definition gives the `R`-linear equivalence between the two. -/
noncomputable
/-
**Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow** 是 Mathlib 中的一个定义，位于命名空间 `Idea
l`。
形式化陈述：powQuotPowSuccLinearEquivMapMkPowSuccPow : ((I ^ n : Ideal R) ⧸ (I • ⊤ : S
ubmodule R (I ^ n : Ideal R))) ≃ₗ[R] Ideal.map (Ideal.Quotient.mk (I ^ (n + 1)))
 (I ^ n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def powQuotPowSuccLinearEquivMapMkPowSuccPow :
    ((I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R))) ≃ₗ[R]
    Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n) := by
  refine { LinearMap.codRestrict
    (Submodule.restrictScalars _ (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)))
    (Submodule.mapQ (I • ⊤) (I ^ (n + 1)) (Submodule.subtype (I ^ n)) ?_) ?_,
    Equiv.ofBijective _ ⟨?_, ?_⟩ with }
  · intro
    simp [Submodule.mem_smul_top_iff, pow_succ']
  · intro x
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [Ideal.mem_sup_left hy]
  · intro a b
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    simp [Ideal.Quotient.eq, Submodule.Quotient.eq, Submodule.mem_smul_top_iff, pow_succ']
  · intro ⟨x, hx⟩
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    simp

/-- `I ^ n ⧸ I ^ (n + 1)` can be viewed as a quotient module and as ideal of `R ⧸ I ^ (n + 1)`.
This definition gives the equivalence between the two, instead of the `R`-linear equivalence,
to bypass typeclass synthesis issues on complex `Module` goals. -/
noncomputable
/-
**Ideal.powQuotPowSuccEquivMapMkPowSuccPow** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：powQuotPowSuccEquivMapMkPowSuccPow : ((I ^ n : Ideal R) ⧸ (I • ⊤ : Submodu
le R (I ^ n : Ideal R))) ≃ Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def powQuotPowSuccEquivMapMkPowSuccPow :
    ((I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R))) ≃
    Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n) :=
  powQuotPowSuccLinearEquivMapMkPowSuccPow I n

end PowQuot

end Ideal

