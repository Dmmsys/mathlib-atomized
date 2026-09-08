/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.Algebra.Central.End
public import Mathlib.Algebra.Central.TensorProduct
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Basic properties of Azumaya algebras

In this file we prove basic facts about Azumaya algebras such as `R` is an Azumaya algebra
over itself where `R` is a commutative ring.

## Main Results

- `IsAzumaya.id`: `R` is an Azumaya algebra over itself.

- `IsAzumaya.ofAlgEquiv`: If `A` is an Azumaya algebra over `R` and `A` is isomorphic to `B`
  as an `R`-algebra, then `B` is an Azumaya algebra over `R`.

## Tags
Noncommutative algebra, Azumaya algebra, Brauer Group

-/

public section

open scoped TensorProduct

open MulOpposite

namespace IsAzumaya

variable (R A B : Type*) [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-
**IsAzumaya.AlgHom.mulLeftRight_bij** 是 Mathlib 中的一个定理，位于命名空间 `IsAzumaya.AlgHom`
。
形式化陈述：∀ (R : Type u_1) (A : Type u_2) [inst : CommSemiring R] [inst_1 : Ring A] 
[inst_2 : Algebra R A] [h : IsAzumaya R A],   Function.Bijective ⇑(AlgHom.mulLef
tRight R A)
参数：R : Type u_1；A : Type u_2；AlgHom.mulLeftRight R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAzumaya.bij`：∀ {R : Type u_1} {A : Type u_2} {inst : CommSemiring R} {
inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : IsAzumaya R A], Function.B
ije…
-/
lemma AlgHom.mulLeftRight_bij [h : IsAzumaya R A] :
    Function.Bijective (AlgHom.mulLeftRight R A) := h.bij

/-- The "canonical" isomorphism between `R ⊗ Rᵒᵖ` and `End R R` which is equal
  to `AlgHom.mulLeftRight R R`. -/
/-
**IsAzumaya.tensorEquivEnd** 是 Mathlib 中的一个缩写定义，位于命名空间 `IsAzumaya`。
形式化陈述：tensorEquivEnd : R otimes[R] Rᵐᵒᵖ ≃ₐ[R] Module.End R R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "canonical" isomorphism between `R ⊗ Rᵒᵖ` and `End R R` which is equal
  to `AlgHom.mulLeftRight R R`.
-/
abbrev tensorEquivEnd : R ⊗[R] Rᵐᵒᵖ ≃ₐ[R] Module.End R R :=
  Algebra.TensorProduct.lid R Rᵐᵒᵖ |>.trans <| .moduleEndSelf R
/-
**IsAzumaya.coe_tensorEquivEnd** 是 Mathlib 中的一个引理，位于命名空间 `IsAzumaya`。
形式化陈述：coe_tensorEquivEnd : tensorEquivEnd R = AlgHom.mulLeftRight R R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext_ring`：∀ {R : Type u_4} {S : Type u_5} {A : Typ
e u_6} {B : Type u_7} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_
2 : Semiring A] [ins…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `AlgEquiv.moduleEndSelf_apply_apply`：∀ (R : Type u_1) {A : Type u_3} [ins
t : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : Aᵐᵒᵖ) (a :
 A),   ((AlgEquiv.module…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `AlgHom.mulLeftRight_apply`：AlgHom.mulLeftRight_apply (a : A) (b : Aᵐᵒᵖ) 
(x : A) : AlgHom.mulLeftRight R A (a otimesₜ b) x = a * x * b.unop
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_tensorEquivEnd : tensorEquivEnd R = AlgHom.mulLeftRight R R := by
  ext; simp
/-
**IsAzumaya.id** 是 Mathlib 中的一个实例，位于命名空间 `IsAzumaya`。
形式化陈述：id : IsAzumaya R R where .bijective bij
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `instFaithfulSMul`：∀ (R : Type u_4) [inst : MulOneClass R], FaithfulSMul 
R R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsAzumaya.coe_tensorEquivEnd`：coe_tensorEquivEnd : tensorEquivEnd R = Al
gHom.mulLeftRight R R
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
instance id : IsAzumaya R R where
  bij := by rw [← coe_tensorEquivEnd]; exact tensorEquivEnd R |>.bijective

/--
The following diagram commutes:
```
          e ⊗ eᵒᵖ
A ⊗ Aᵐᵒᵖ  ------------> B ⊗ Bᵐᵒᵖ
  |                        |
  |                        |
  | mulLeftRight R A       | mulLeftRight R B
  |                        |
  V                        V
End R A   ------------> End R B
          e.conj
```
-/
/-
**IsAzumaya.mulLeftRight_comp_congr** 是 Mathlib 中的一个引理，位于命名空间 `IsAzumaya`。
形式化陈述：mulLeftRight_comp_congr (e : A ≃ₐ[R] B) : (AlgHom.mulLeftRight R B).comp (
Algebra.TensorProduct.congr e e.op).toAlgHom = (e.toLinearEquiv.conjAlgEquiv R).
toAlgHom.comp (AlgHom.mulLeftRight R A)
参数：e : A ≃ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
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
· 使用定理 `AlgEquiv.op_apply_apply`：∀ {R : Type u_1} {A : Type u_3} {B : Type u_4} 
[inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : 
Algebra R A] …
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
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用引理 `AlgHom.mulLeftRight_apply`：AlgHom.mulLeftRight_apply (a : A) (b : Aᵐᵒᵖ) 
(x : A) : AlgHom.mulLeftRight R A (a otimesₜ b) x = a * x * b.unop
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LinearEquiv.conjAlgEquiv_apply_apply`：∀ (R : Type u_1) {S : Type u_2} {M
₁ : Type u_3} {M₂ : Type u_4} [inst : CommSemiring R] [inst_1 : AddCommMonoid M₁
]   [inst_2 : _root_.Modul…
· 使用定理 `AlgEquiv.toLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The following diagram commutes:
```
          e ⊗ eᵒᵖ
A ⊗ Aᵐᵒᵖ  ------------> B ⊗ Bᵐᵒᵖ
  |                        |
  |                        |
  | mulLeftRight R A       | mulLeftRight R B
  |                        |
  V                        V
End R A   ------------> End R B
          e.conj
```
-/
lemma mulLeftRight_comp_congr (e : A ≃ₐ[R] B) :
    (AlgHom.mulLeftRight R B).comp (Algebra.TensorProduct.congr e e.op).toAlgHom =
    (e.toLinearEquiv.conjAlgEquiv R).toAlgHom.comp (AlgHom.mulLeftRight R A) := by
  ext <;> simp
/-
**IsAzumaya.of_AlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `IsAzumaya`。
形式化陈述：of_AlgEquiv (e : A ≃ₐ[R] B) [IsAzumaya R A] : IsAzumaya R B
参数：e : A ≃ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_equiv`：∀ {R : Type u_8} {S : Type u_9} [inst : Semi
ring R] [inst_1 : Semiring S] {M : Type u_10} {N : Type u_11}   [inst_2 : AddCom
mMonoid M] [inst…
· 使用定理 `IsAzumaya.toProjective`：∀ {R : Type u_1} {A : Type u_2} {inst : CommSemi
ring R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : IsAzumaya R A], M
odule.Projec…
· 使用定理 `FaithfulSMul.of_injective`：∀ {M' : Type u_1} {X : Type u_5} [inst : SMul
 M' X] {Y : Type u_6} [inst_1 : SMul M' Y] {F : Type u_8}   [inst_2 : FunLike F 
X Y] [FaithfulS…
· 使用定理 `IsAzumaya.toFaithfulSMul`：∀ {R : Type u_1} {A : Type u_2} {inst : CommSe
miring R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : IsAzumaya R A],
 FaithfulSMul …
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用定理 `IsAzumaya.toFinite`：∀ {R : Type u_1} {A : Type u_2} {inst : CommSemiring
 R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : IsAzumaya R A], Modul
e.Finite…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.coe_toAlgHom`：coe_toAlgHom : DFunLike.coe e.toAlgHom = e
· 使用定理 `AlgHom.coe_comp`：coe_comp (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) : ⇑(φ₁.com
p φ₂) = φ₁ ∘ φ₂
· 使用引理 `IsAzumaya.mulLeftRight_comp_congr`：mulLeftRight_comp_congr (e : A ≃ₐ[R] 
B) : (AlgHom.mulLeftRight R B).comp (Algebra.TensorProduct.congr e e.op).toAlgHo
m = (e.toLinearEquiv.co…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem of_AlgEquiv (e : A ≃ₐ[R] B) [IsAzumaya R A] : IsAzumaya R B :=
  let _ : Module.Projective R B := .of_equiv e.toLinearEquiv
  let _ : FaithfulSMul R B := .of_injective e e.injective
  let _ : Module.Finite R B := .equiv e.toLinearEquiv
  ⟨Function.Bijective.of_comp_iff (AlgHom.mulLeftRight R B)
    (Algebra.TensorProduct.congr e e.op).bijective |>.1 <| by
    rw [← AlgEquiv.coe_toAlgHom, ← AlgHom.coe_comp, mulLeftRight_comp_congr]
    simp [AlgHom.mulLeftRight_bij]⟩

end IsAzumaya

/-- An Azumaya algebra is a central algebra. -/
/-
**Algebra.IsCentral.instIsAzumaya** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.IsCentral.instIsAzumaya {R A : Type*} [CommSemiring R] [Semiring A
] [Algebra R A] [Module.Free R A] [IsAzumaya R A] : IsCentral R A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.IsCentral.of_algEquiv`：of_algEquiv (e : D ≃ₐ[K] D') : IsCentral 
K D' where out x hx
· 使用定理 `Algebra.IsCentral.instEnd`：∀ {R : Type u_1} {S : Type u_2} {M : Type u_3
} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[Module.Free R …
· 使用定理 `IsAzumaya.bij`：∀ {R : Type u_1} {A : Type u_2} {inst : CommSemiring R} {
inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : IsAzumaya R A], Function.B
ije…
· 使用引理 `Algebra.IsCentral.left_of_tensor`：left_of_tensor (inj : Function.Injecti
ve (algebraMap K C)) [Module.Flat K B] [hbc : Algebra.IsCentral K (B otimes[K] C
)] : IsCentral K B whe…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `instFaithfulSMulMulOpposite_1`：∀ {M : Type u_1} {α : Type u_3} [inst : S
Mul α M] [FaithfulSMul α M], FaithfulSMul α Mᵐᵒᵖ
· 使用定理 `IsAzumaya.toFaithfulSMul`：∀ {R : Type u_1} {A : Type u_2} {inst : CommSe
miring R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : IsAzumaya R A],
 FaithfulSMul …

--- 原说明 ---
An Azumaya algebra is a central algebra.
-/
instance Algebra.IsCentral.instIsAzumaya {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [Module.Free R A] [IsAzumaya R A] : IsCentral R A :=
  have := of_algEquiv R _ _ (AlgEquiv.ofBijective (.mulLeftRight R A) IsAzumaya.bij).symm
  left_of_tensor R A Aᵐᵒᵖ <| FaithfulSMul.algebraMap_injective _ _
