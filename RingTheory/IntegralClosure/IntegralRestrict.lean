/-
Copyright (c) 2023 Andrew Yang, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Restriction of various maps between fields to integrally closed subrings.

In this file, we assume `A` is an integrally closed domain; `K` is the fraction ring of `A`;
`L` is a finite extension of `K`; `B` is the integral closure of `A` in `L`.
We call this the AKLB setup.

## Main definitions
- `galRestrict`: The restriction `Aut(L/K) → Aut(B/A)` as an `MulEquiv` in an AKLB setup.
- `Algebra.intTrace`: The trace map of a finite extension of integrally closed domains `B/A` is
  defined to be the restriction of the trace map of `Frac(B)/Frac(A)`.
- `Algebra.intNorm`: The norm map of a finite extension of integrally closed domains `B/A` is
  defined to be the restriction of the norm map of `Frac(B)/Frac(A)`.

-/

@[expose] public section

open Module nonZeroDivisors

variable (A K L L₂ L₃ B B₂ B₃ : Type*)
variable [CommRing A] [CommRing B] [CommRing B₂] [CommRing B₃]
variable [Algebra A B] [Algebra A B₂] [Algebra A B₃]
variable [Field K] [Field L] [Field L₂] [Field L₃]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [Algebra K L₂] [Algebra A L₂] [IsScalarTower A K L₂]
variable [Algebra K L₃] [Algebra A L₃] [IsScalarTower A K L₃]
variable [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
variable [Algebra B₂ L₂] [IsScalarTower A B₂ L₂] [IsIntegralClosure B₂ A L₂]
variable [Algebra B₃ L₃] [IsScalarTower A B₃ L₃] [IsIntegralClosure B₃ A L₃]

section galois

section galRestrict'
variable {K L L₂ L₃}
omit [IsFractionRing A K]

/-- A generalization of `galRestrictHom` beyond endomorphisms. -/
noncomputable
/-
**galRestrict'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：galRestrict' (f : L ->ₐ[K] L₂) : (B ->ₐ[A] B₂)
参数：f : L ->ₐ[K] L₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def galRestrict' (f : L →ₐ[K] L₂) : (B →ₐ[A] B₂) :=
  (IsIntegralClosure.equiv A (integralClosure A L₂) L₂ B₂).toAlgHom.comp
      (((f.restrictScalars A).comp (IsScalarTower.toAlgHom A B L)).codRestrict
        (integralClosure A L₂) (fun x ↦ IsIntegral.map _ (IsIntegralClosure.isIntegral A L x)))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**algebraMap_galRestrict'_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (A : Type u_1) {K : Type u_2} {L : Type u_3} {L₂ : Type u_4} (B : Type u
_6) (B₂ : Type u_7) [inst : CommRing A]   [inst_1 : CommRing B] [inst_2 : CommRi
ng B₂] [inst_3 : Algebra A B] [inst_4 : Algebra A B₂] [inst_5 : Field K]   [inst
_6 : Field L] [inst_7 : Field L₂] [inst_8 : Algebra A K] [inst_9 : Algebra K L] 
[inst_10 : Algebra A L]   [inst_11 : IsScalarTower A K L] [inst_12 : Algebra K L
₂] [inst_13 : Algebra A L₂] [inst_14 : IsScalarTower A K L₂]   [inst_15 : Algebr
a B L] [inst_16 : IsScalarTower A B L] [inst_17 : IsIntegralClosure B A L] [inst
_18 : Algebra B₂ L₂]   [inst_19 : IsScalarTower A B₂ L₂] [inst_20 : IsIntegralCl
osure B₂ A L₂] (σ : L →ₐ[K] L₂) (x : B),   (algebraMap B₂ L₂) ((galRestrict' A B
 B₂ σ) x) = σ ((algebraMap B L) x)
参数：A : Type u_1；B : Type u_6；B₂ : Type u_7；σ : L →ₐ[K] L₂；x : B；algebraMap B₂ L₂
；(galRestrict' A B B₂ σ) x；(algebraMap B L) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsIntegralClosure.algebraMap_equiv`：algebraMap_equiv (x : A) : algebraMa
p A' B (equiv R A B A' x) = algebraMap A B x
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma algebraMap_galRestrict'_apply (σ : L →ₐ[K] L₂) (x : B) :
    algebraMap B₂ L₂ (galRestrict' A B B₂ σ x) = σ (algebraMap B L x) := by
  simp [galRestrict', galRestrict', Subalgebra.algebraMap_eq]

@[simp]
/-
**galRestrict'_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (A : Type u_1) {K : Type u_2} {L : Type u_3} (B : Type u_6) [inst : Comm
Ring A] [inst_1 : CommRing B]   [inst_2 : Algebra A B] [inst_3 : Field K] [inst_
4 : Field L] [inst_5 : Algebra A K] [inst_6 : Algebra K L]   [inst_7 : Algebra A
 L] [inst_8 : IsScalarTower A K L] [inst_9 : Algebra B L] [inst_10 : IsScalarTow
er A B L]   [inst_11 : IsIntegralClosure B A L], galRestrict' A B B (AlgHom.id K
 L) = AlgHom.id A B
参数：A : Type u_1；B : Type u_6；AlgHom.id K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraMap_galRestrict'_apply`：∀ (A : Type u_1) {K : Type u_2} {L : Type
 u_3} {L₂ : Type u_4} (B : Type u_6) (B₂ : Type u_7) [inst : CommRing A]   [inst
_1 : CommRing B] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem galRestrict'_id : galRestrict' A B B (.id K L) = .id A B := by
  ext
  apply IsIntegralClosure.algebraMap_injective B A L
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**galRestrict'_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (A : Type u_1) {K : Type u_2} {L : Type u_3} {L₂ : Type u_4} {L₃ : Type 
u_5} (B : Type u_6) (B₂ : Type u_7)   (B₃ : Type u_8) [inst : CommRing A] [inst_
1 : CommRing B] [inst_2 : CommRing B₂] [inst_3 : CommRing B₃]   [inst_4 : Algebr
a A B] [inst_5 : Algebra A B₂] [inst_6 : Algebra A B₃] [inst_7 : Field K] [inst_
8 : Field L]   [inst_9 : Field L₂] [inst_10 : Field L₃] [inst_11 : Algebra A K] 
[inst_12 : Algebra K L] [inst_13 : Algebra A L]   [inst_14 : IsScalarTower A K L
] [inst_15 : Algebra K L₂] [inst_16 : Algebra A L₂] [inst_17 : IsScalarTower A K
 L₂]   [inst_18 : Algebra K L₃] [inst_19 : Algebra A L₃] [inst_20 : IsScalarTowe
r A K L₃] [inst_21 : Algebra B L]   [inst_22 : IsScalarTower A B L] [inst_23 : I
sIntegralClosure B A L] [inst_24 : Algebra B₂ L₂]   [inst_25 : IsScalarTower A B
₂ L₂] [inst_26 : IsIntegralClosure B₂ A L₂] [inst_27 : Algebra B₃ L₃]   [inst_28
 : IsScalarTower A B₃ L₃] [inst_29 : IsIntegralClosure B₃ A L₃] (σ : L →ₐ[K] L₂)
 (σ' : L₂ →ₐ[K] L₃),   galRestrict' A B B₃ (σ'.comp σ) = (galRestrict' A B₂ B₃ σ
').comp (galRestrict' A B B₂ σ)
参数：A : Type u_1；B : Type u_6；B₂ : Type u_7；B₃ : Type u_8；σ : L →ₐ[K] L₂；σ' : L₂ 
→ₐ[K] L₃；σ'.comp σ；galRestrict' A B₂ B₃ σ'；galRestrict' A B B₂ σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsIntegralClosure.algebraMap_equiv`：algebraMap_equiv (x : A) : algebraMa
p A' B (equiv R A B A' x) = algebraMap A B x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem galRestrict'_comp (σ : L →ₐ[K] L₂) (σ' : L₂ →ₐ[K] L₃) :
    galRestrict' A B B₃ (σ'.comp σ) = (galRestrict' A B₂ B₃ σ').comp (galRestrict' A B B₂ σ) := by
  ext x
  apply (IsIntegralClosure.equiv A (integralClosure A L₃) L₃ B₃).symm.injective
  ext
  simp [galRestrict', Subalgebra.algebraMap_eq]

end galRestrict'

variable [Algebra.IsAlgebraic K L]

section galLift
variable {A B B₂ B₃}

/-- A generalization of the lift `End(B/A) → End(L/K)` in an ALKB setup.
This is inverse to the restriction. See `galRestrictHom`. -/
noncomputable
/-
**galLift** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：galLift (σ : B ->ₐ[A] B₂) : L ->ₐ[K] L₂
参数：σ : B ->ₐ[A] B₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def galLift (σ : B →ₐ[A] B₂) : L →ₐ[K] L₂ :=
  haveI := (IsFractionRing.injective A K).isDomain
  haveI := IsTorsionFree.trans_faithfulSMul A K L₂
  haveI := IsIntegralClosure.isLocalization A K L B
  haveI H : ∀ (y : Algebra.algebraMapSubmonoid B A⁰),
      IsUnit (((algebraMap B₂ L₂).comp σ) (y : B)) := by
    rintro ⟨_, x, hx, rfl⟩
    simpa only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgHom.commutes,
      isUnit_iff_ne_zero, ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _),
      ← IsScalarTower.algebraMap_apply] using nonZeroDivisors.ne_zero hx
  haveI H_eq : (IsLocalization.lift (S := L) H).comp (algebraMap K L) = (algebraMap K L₂) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, ← IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply A K L₂,
      IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B₂ L₂,
      IsLocalization.lift_eq, RingHom.coe_coe, AlgHom.commutes]
  { IsLocalization.lift (S := L) H with commutes' := DFunLike.congr_fun H_eq }

omit [IsIntegralClosure B₂ A L₂] in
@[simp]
/-
**galLift_algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：galLift_algebraMap_apply (σ : B ->ₐ[A] B₂) (x : B) : galLift K L L₂ σ (alg
ebraMap B L x) = algebraMap B₂ L₂ (σ x)
参数：σ : B ->ₐ[A] B₂；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.lift_eq`：lift_eq (x : R) : lift hg ((algebraMap R S) x) =
 g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem galLift_algebraMap_apply (σ : B →ₐ[A] B₂) (x : B) :
    galLift K L L₂ σ (algebraMap B L x) = algebraMap B₂ L₂ (σ x) := by
  simp [galLift]

@[simp]
/-
**galLift_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：galLift_id : galLift K L L (.id A B) = .id K L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `IsLocalization.lift.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring R]
 {M M_1 : Submonoid R} (e_M : M = M_1) {S : Type u_2} [inst_1 : CommSemiring S] 
  [inst_2 : Algebra …
· 使用定理 `AlgHom.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R
 A] [inst_…
· 使用定理 `IsLocalization.lift_id`：lift_id (x) : lift (map_units S : forall _ : M, 
IsUnit _) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem galLift_id : galLift K L L (.id A B) = .id K L := by
  ext; simp [galLift]

omit [IsIntegralClosure B₃ A L₃] in
/-
**galLift_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：galLift_comp [Algebra.IsAlgebraic K L₂] (σ : B ->ₐ[A] B₂) (σ' : B₂ ->ₐ[A] 
B₃) : galLift K L L₃ (σ'.comp σ) = (galLift K L₂ L₃ σ').comp (galLift K L L₂ σ)
参数：σ : B ->ₐ[A] B₂；σ' : B₂ ->ₐ[A] B₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `IsIntegralClosure.isLocalization`：IsIntegralClosure.isLocalization [IsDo
main A] [Algebra.IsAlgebraic K L] : IsLocalization (Algebra.algebraMapSubmonoid 
C A⁰) L
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `galLift_algebraMap_apply`：galLift_algebraMap_apply (σ : B ->ₐ[A] B₂) (x 
: B) : galLift K L L₂ σ (algebraMap B L x) = algebraMap B₂ L₂ (σ x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem galLift_comp [Algebra.IsAlgebraic K L₂] (σ : B →ₐ[A] B₂) (σ' : B₂ →ₐ[A] B₃) :
    galLift K L L₃ (σ'.comp σ) = (galLift K L₂ L₃ σ').comp (galLift K L L₂ σ) :=
  have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
  AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
    <| RingHom.ext fun x ↦ by simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**galLift_galRestrict'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：galLift_galRestrict' (σ : L ->ₐ[K] L₂) : galLift K L L₂ (galRestrict' A B 
B₂ σ) = σ
参数：σ : L ->ₐ[K] L₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `IsIntegralClosure.isLocalization`：IsIntegralClosure.isLocalization [IsDo
main A] [Algebra.IsAlgebraic K L] : IsLocalization (Algebra.algebraMapSubmonoid 
C A⁰) L
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.lift_comp`：lift_comp : (lift hg).comp (algebraMap R S) = 
g
· 使用定理 `IsIntegralClosure.algebraMap_equiv`：algebraMap_equiv (x : A) : algebraMa
p A' B (equiv R A B A' x) = algebraMap A B x
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem galLift_galRestrict' (σ : L →ₐ[K] L₂) :
    galLift K L L₂ (galRestrict' A B B₂ σ) = σ :=
  have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
  AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
    <| RingHom.ext fun x ↦ by simp [galRestrict', Subalgebra.algebraMap_eq, galLift]

@[simp]
/-
**galRestrict'_galLift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {A : Type u_1} (K : Type u_2) (L : Type u_3) (L₂ : Type u_4) {B : Type u
_6} {B₂ : Type u_7} [inst : CommRing A]   [inst_1 : CommRing B] [inst_2 : CommRi
ng B₂] [inst_3 : Algebra A B] [inst_4 : Algebra A B₂] [inst_5 : Field K]   [inst
_6 : Field L] [inst_7 : Field L₂] [inst_8 : Algebra A K] [inst_9 : IsFractionRin
g A K] [inst_10 : Algebra K L]   [inst_11 : Algebra A L] [inst_12 : IsScalarTowe
r A K L] [inst_13 : Algebra K L₂] [inst_14 : Algebra A L₂]   [inst_15 : IsScalar
Tower A K L₂] [inst_16 : Algebra B L] [inst_17 : IsScalarTower A B L]   [inst_18
 : IsIntegralClosure B A L] [inst_19 : Algebra B₂ L₂] [inst_20 : IsScalarTower A
 B₂ L₂]   [inst_21 : IsIntegralClosure B₂ A L₂] [inst_22 : Algebra.IsAlgebraic K
 L] (σ : B →ₐ[A] B₂),   galRestrict' A B B₂ (galLift K L L₂ σ) = σ
参数：K : Type u_2；L : Type u_3；L₂ : Type u_4；σ : B →ₐ[A] B₂；galLift K L L₂ σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `IsIntegralClosure.isLocalization`：IsIntegralClosure.isLocalization [IsDo
main A] [Algebra.IsAlgebraic K L] : IsLocalization (Algebra.algebraMapSubmonoid 
C A⁰) L
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraMap_galRestrict'_apply`：∀ (A : Type u_1) {K : Type u_2} {L : Type
 u_3} {L₂ : Type u_4} (B : Type u_6) (B₂ : Type u_7) [inst : CommRing A]   [inst
_1 : CommRing B] [i…
· 使用定理 `galLift_algebraMap_apply`：galLift_algebraMap_apply (σ : B ->ₐ[A] B₂) (x 
: B) : galLift K L L₂ σ (algebraMap B L x) = algebraMap B₂ L₂ (σ x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem galRestrict'_galLift (σ : B →ₐ[A] B₂) :
    galRestrict' A B B₂ (galLift K L L₂ σ) = σ :=
  have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
  AlgHom.ext fun x ↦ IsIntegralClosure.algebraMap_injective B₂ A L₂
    (by simp)

/--
A version of `galLift` for `AlgEquiv`.
-/
@[simps! -fullyApplied apply symm_apply]
noncomputable
/-
**galLiftEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：galLiftEquiv [Algebra.IsAlgebraic K L₂] (σ : B ≃ₐ[A] B₂) : L ≃ₐ[K] L₂
参数：σ : B ≃ₐ[A] B₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def galLiftEquiv [Algebra.IsAlgebraic K L₂] (σ : B ≃ₐ[A] B₂) : L ≃ₐ[K] L₂ :=
  AlgEquiv.ofAlgHom (galLift K L L₂ σ.toAlgHom) (galLift K L₂ L σ.symm.toAlgHom)
  (by simp [← galLift_comp]) (by simp [← galLift_comp])
/-
**galLiftEquiv_algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：galLiftEquiv_algebraMap_apply [Algebra.IsAlgebraic K L₂] (σ : B ≃ₐ[A] B₂) 
(x : B) : galLiftEquiv K L L₂ σ (algebraMap B L x) = algebraMap B₂ L₂ (σ x)
参数：σ : B ≃ₐ[A] B₂；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂}
 [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3
 : Algebra R …
· 使用定理 `galLift_algebraMap_apply`：galLift_algebraMap_apply (σ : B ->ₐ[A] B₂) (x 
: B) : galLift K L L₂ σ (algebraMap B L x) = algebraMap B₂ L₂ (σ x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem galLiftEquiv_algebraMap_apply [Algebra.IsAlgebraic K L₂] (σ : B ≃ₐ[A] B₂) (x : B) :
    galLiftEquiv K L L₂ σ (algebraMap B L x) = algebraMap B₂ L₂ (σ x) := by
  simp [galLiftEquiv]

end galLift

/-- The restriction `End(L/K) → End(B/A)` in an AKLB setup.
Also see `galRestrict` for the `AlgEquiv` version. -/
@[simps -isSimp]
noncomputable
/-
**galRestrictHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：galRestrictHom : (L ->ₐ[K] L) ≃* (B ->ₐ[A] B) where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `galLift_galRestrict'`：galLift_galRestrict' (σ : L ->ₐ[K] L₂) : galLift K
 L L₂ (galRestrict' A B B₂ σ) = σ
· 使用定理 `galRestrict'_galLift`：∀ {A : Type u_1} (K : Type u_2) (L : Type u_3) (L₂
 : Type u_4) {B : Type u_6} {B₂ : Type u_7} [inst : CommRing A]   [inst_1 : Comm
Ring B] [i…
· 使用定理 `galRestrict'_comp`：∀ (A : Type u_1) {K : Type u_2} {L : Type u_3} {L₂ : 
Type u_4} {L₃ : Type u_5} (B : Type u_6) (B₂ : Type u_7)   (B₃ : Type u_8) [inst
 : Comm…
-/
def galRestrictHom : (L →ₐ[K] L) ≃* (B →ₐ[A] B) where
  toFun f := galRestrict' A B B f
  map_mul' σ₁ σ₂ := galRestrict'_comp _ _ _ _ σ₂ σ₁
  invFun := galLift K L L
  left_inv σ := galLift_galRestrict' _ _ _ σ
  right_inv σ := galRestrict'_galLift _ _ _ σ

@[simp]
/-
**algebraMap_galRestrictHom_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_galRestrictHom_apply (σ : L ->ₐ[K] L) (x : B) : algebraMap B L 
(galRestrictHom A K L B σ x) = σ (algebraMap B L x)
参数：σ : L ->ₐ[K] L；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraMap_galRestrict'_apply`：∀ (A : Type u_1) {K : Type u_2} {L : Type
 u_3} {L₂ : Type u_4} (B : Type u_6) (B₂ : Type u_7) [inst : CommRing A]   [inst
_1 : CommRing B] [i…
-/
lemma algebraMap_galRestrictHom_apply (σ : L →ₐ[K] L) (x : B) :
    algebraMap B L (galRestrictHom A K L B σ x) = σ (algebraMap B L x) :=
  algebraMap_galRestrict'_apply _ _ _ _ _

@[simp, nolint unusedHavesSuffices] -- false positive from unfolding galRestrictHom
/-
**galRestrictHom_symm_algebraMap_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：galRestrictHom_symm_algebraMap_apply (σ : B ->ₐ[A] B) (x : B) : (galRestri
ctHom A K L B).symm σ (algebraMap B L x) = algebraMap B L (σ x)
参数：σ : B ->ₐ[A] B；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `galLift_algebraMap_apply`：galLift_algebraMap_apply (σ : B ->ₐ[A] B₂) (x 
: B) : galLift K L L₂ σ (algebraMap B L x) = algebraMap B₂ L₂ (σ x)
-/
lemma galRestrictHom_symm_algebraMap_apply (σ : B →ₐ[A] B) (x : B) :
    (galRestrictHom A K L B).symm σ (algebraMap B L x) = algebraMap B L (σ x) :=
  galLift_algebraMap_apply _ _ _ _ _

/-- The restriction `Aut(L/K) → Aut(B/A)` in an AKLB setup. -/
noncomputable
/-
**galRestrict** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：galRestrict : Gal(L/K) ≃* (B ≃ₐ[A] B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def galRestrict : Gal(L/K) ≃* (B ≃ₐ[A] B) :=
  (AlgEquiv.algHomUnitsEquiv K L).symm.trans
    ((Units.mapEquiv <| galRestrictHom A K L B).trans (AlgEquiv.algHomUnitsEquiv A B))

variable {K L}
/-
**coe_galRestrict_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_galRestrict_apply (σ : Gal(L/K)) : (galRestrict A K L B σ : B ->ₐ[A] B
) = galRestrictHom A K L B σ
参数：σ : Gal(L/K)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_galRestrict_apply (σ : Gal(L/K)) :
    (galRestrict A K L B σ : B →ₐ[A] B) = galRestrictHom A K L B σ := rfl

variable {B}
/-
**galRestrict_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：galRestrict_apply (σ : Gal(L/K)) (x : B) : galRestrict A K L B σ x = galRe
strictHom A K L B σ x
参数：σ : Gal(L/K)；x : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma galRestrict_apply (σ : Gal(L/K)) (x : B) :
    galRestrict A K L B σ x = galRestrictHom A K L B σ x := rfl
/-
**algebraMap_galRestrict_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_galRestrict_apply (σ : Gal(L/K)) (x : B) : algebraMap B L (galR
estrict A K L B σ x) = σ (algebraMap B L x)
参数：σ : Gal(L/K)；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `algebraMap_galRestrictHom_apply`：algebraMap_galRestrictHom_apply (σ : L 
->ₐ[K] L) (x : B) : algebraMap B L (galRestrictHom A K L B σ x) = σ (algebraMap 
B L x)
-/
lemma algebraMap_galRestrict_apply (σ : Gal(L/K)) (x : B) :
    algebraMap B L (galRestrict A K L B σ x) = σ (algebraMap B L x) :=
  algebraMap_galRestrictHom_apply A K L B σ.toAlgHom x

variable (K) in
/-
**galRestrict_symm_algebraMap_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：galRestrict_symm_algebraMap_apply (σ : B ≃ₐ[A] B) (x : B) : (galRestrict A
 K L B).symm σ (algebraMap B L x) = algebraMap B L (σ x)
参数：σ : B ≃ₐ[A] B；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `galRestrictHom_symm_algebraMap_apply`：galRestrictHom_symm_algebraMap_app
ly (σ : B ->ₐ[A] B) (x : B) : (galRestrictHom A K L B).symm σ (algebraMap B L x)
 = algebraMap B L (σ x)
-/
lemma galRestrict_symm_algebraMap_apply (σ : B ≃ₐ[A] B) (x : B) :
    (galRestrict A K L B).symm σ (algebraMap B L x) = algebraMap B L (σ x) :=
  galRestrictHom_symm_algebraMap_apply A K L B σ x

end galois

variable [FiniteDimensional K L]

/-
**prod_galRestrict_eq_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：prod_galRestrict_eq_norm [IsGalois K L] [IsIntegrallyClosed A] (x : B) : (
∏ σ : Gal(L/K), galRestrict A K L B σ x) = algebraMap A B (IsIntegralClosure.mk'
 (R
参数：x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `IsPurelyInseparable.isIntegral`：∀ {F : Type u_1} {E : Type u_2} {inst : 
CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInseparab
le F E], Algebra.IsI…
· 使用定理 `Algebra.isIntegral_norm`：isIntegral_norm [Algebra R L] [Algebra R K] [Is
ScalarTower R K L] {x : L} (hx : IsIntegral R x) : IsIntegral R (norm K x)
· 使用定理 `IsIntegral.algebraMap`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra R 
A] [inst_4 …
· 使用定理 `IsIntegralClosure.isIntegral`：∀ (R : Type u_1) {A : Type u_2} (B : Type 
u_3) [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : CommRing B]   [inst_3 :
 Algebra R B] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `algebraMap_galRestrict_apply`：algebraMap_galRestrict_apply (σ : Gal(L/K)
) (x : B) : algebraMap B L (galRestrict A K L B σ x) = σ (algebraMap B L x)
· 使用定理 `IsIntegralClosure.algebraMap_mk'`：algebraMap_mk' (x : B) (hx : IsIntegra
l R x) : algebraMap A B (mk' A x hx) = x
· 使用定理 `Algebra.norm_eq_prod_automorphisms`：norm_eq_prod_automorphisms [IsGalois
 K L] (x : L) : algebraMap K L (norm K x) = ∏ σ : Gal(L/K), σ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_galRestrict_eq_norm [IsGalois K L] [IsIntegrallyClosed A] (x : B) :
    (∏ σ : Gal(L/K), galRestrict A K L B σ x) =
    algebraMap A B (IsIntegralClosure.mk' (R := A) A (Algebra.norm K <| algebraMap B L x)
      (Algebra.isIntegral_norm K (IsIntegralClosure.isIntegral A L x).algebraMap)) := by
  apply IsIntegralClosure.algebraMap_injective B A L
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_eq A K L]
  simp only [map_prod, algebraMap_galRestrict_apply, IsIntegralClosure.algebraMap_mk',
    Algebra.norm_eq_prod_automorphisms, RingHom.coe_comp, Function.comp_apply]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

noncomputable
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [IsDomain A] [IsDomain B] [IsIntegrallyClosed B]
    [Module.Finite A B] [IsTorsionFree A B] : Fintype (B ≃ₐ[A] B) :=
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  haveI : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  Fintype.ofEquiv _ (galRestrict A (FractionRing A) (FractionRing B) B).toEquiv

variable {Aₘ Bₘ} [CommRing Aₘ] [CommRing Bₘ] [Algebra Aₘ Bₘ] [Algebra A Aₘ] [Algebra B Bₘ]
variable [Algebra A Bₘ] [IsScalarTower A Aₘ Bₘ] [IsScalarTower A B Bₘ]
variable (M : Submonoid A) [IsLocalization M Aₘ]
variable [IsLocalization (Algebra.algebraMapSubmonoid B M) Bₘ]

section trace

/-- The restriction of the trace on `L/K` restricted onto `B/A` in an AKLB setup.
See `Algebra.intTrace` instead. -/
noncomputable
/-
**Algebra.intTraceAux** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.intTraceAux [IsIntegrallyClosed A] : B ->ₗ[A] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Algebra.intTraceAux [IsIntegrallyClosed A] :
    B →ₗ[A] A :=
  (IsIntegralClosure.equiv A (integralClosure A K) K A).toLinearMap.comp
    ((((Algebra.trace K L).restrictScalars A).comp
      (IsScalarTower.toAlgHom A B L).toLinearMap).codRestrict
        (Subalgebra.toSubmodule <| integralClosure A K) (fun x ↦ isIntegral_trace
          (IsIntegral.algebraMap (IsIntegralClosure.isIntegral A L x))))

variable {A K L B}
/-
**Algebra.map_intTraceAux** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.map_intTraceAux [IsIntegrallyClosed A] (x : B) : algebraMap A K (A
lgebra.intTraceAux A K L B x) = Algebra.trace K L (algebraMap B L x)
参数：x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.algebraMap_equiv`：algebraMap_equiv (x : A) : algebraMa
p A' B (equiv R A B A' x) = algebraMap A B x
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `IsPurelyInseparable.isIntegral`：∀ {F : Type u_1} {E : Type u_2} {inst : 
CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInseparab
le F E], Algebra.IsI…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma Algebra.map_intTraceAux [IsIntegrallyClosed A] (x : B) :
    algebraMap A K (Algebra.intTraceAux A K L B x) = Algebra.trace K L (algebraMap B L x) :=
  IsIntegralClosure.algebraMap_equiv A (integralClosure A K) K A _

variable (A B)
variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]
variable [Module.Finite A B] [IsTorsionFree A B]

/-- The trace of a finite extension of integrally closed domains `B/A` is the restriction of
the trace on `Frac(B)/Frac(A)` onto `B/A`. See `Algebra.algebraMap_intTrace`. -/
noncomputable
/-
**Algebra.intTrace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.intTrace : B ->ₗ[A] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Algebra.intTrace : B →ₗ[A] A :=
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  haveI : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  Algebra.intTraceAux A (FractionRing A) (FractionRing B) B

variable {A B}
/-
**Algebra.algebraMap_intTrace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.algebraMap_intTrace (x : B) : algebraMap A K (Algebra.intTrace A B
 x) = Algebra.trace K L (algebraMap B L x)
参数：x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `isAlgebraic_of_isFractionRing`：isAlgebraic_of_isFractionRing (R S K L) [
CommRing R] [CommRing S] [Field K] [CommRing L] [Algebra R S] [Algebra R K] [Alg
ebra R L] [Algebra …
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsIntegralClosure.isLocalization`：IsIntegralClosure.isLocalization [IsDo
main A] [Algebra.IsAlgebraic K L] : IsLocalization (Algebra.algebraMapSubmonoid 
C A⁰) L
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `Module.Finite.of_isLocalization`：of_isLocalization (R S) {Rₚ Sₚ : Type*}
 [CommSemiring R] [CommSemiring S] [CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra 
R S] [Algebra R Rₚ] […
· 使用定理 `IsIntegralClosure.isFractionRing_of_finite_extension`：isFractionRing_of_
finite_extension [IsDomain A] [Algebra K L] [IsScalarTower A K L] [FiniteDimensi
onal K L] : IsFractionRing C L
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `Algebra.intTrace.eq_1`：∀ (A : Type u_1) (B : Type u_6) [inst : CommRing 
A] [inst_1 : CommRing B] [inst_2 : Algebra A B] [inst_3 : IsDomain A]   [inst_4 
: IsIntegra…
· 使用引理 `Algebra.map_intTraceAux`：Algebra.map_intTraceAux [IsIntegrallyClosed A] 
(x : B) : algebraMap A K (Algebra.intTraceAux A K L B x) = Algebra.trace K L (al
gebraMap B L …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.trace_eq_of_equiv_equiv`：Algebra.trace_eq_of_equiv_equiv {A₁ B₁ 
A₂ B₂ : Type*} [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂] [Algebra 
A₁ B₁] [Algebra A₂ B₂…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsFractionRing.algEquiv_commutes`：algEquiv_commutes (e : K₁ ≃ₐ[A] K₂) (f
 : L₁ ≃ₐ[B] L₂) (x : K₁) : algebraMap K₂ L₂ (e x) = f (algebraMap K₁ L₁ x)
-/
lemma Algebra.algebraMap_intTrace (x : B) :
    algebraMap A K (Algebra.intTrace A B x) = Algebra.trace K L (algebraMap B L x) := by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply (FractionRing.algEquiv A K).symm.injective
  rw [AlgEquiv.commutes, Algebra.intTrace, Algebra.map_intTraceAux,
    ← AlgEquiv.commutes (FractionRing.algEquiv B L)]
  apply Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv
  ext
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _
/-
**Algebra.algebraMap_intTrace_fractionRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.algebraMap_intTrace_fractionRing (x : B) : algebraMap A (FractionR
ing A) (Algebra.intTrace A B x) = Algebra.trace (FractionRing A) (FractionRing B
) (algebraMap B _ x)
参数：x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `isAlgebraic_of_isFractionRing`：isAlgebraic_of_isFractionRing (R S K L) [
CommRing R] [CommRing S] [Field K] [CommRing L] [Algebra R S] [Algebra R K] [Alg
ebra R L] [Algebra …
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsIntegralClosure.isLocalization`：IsIntegralClosure.isLocalization [IsDo
main A] [Algebra.IsAlgebraic K L] : IsLocalization (Algebra.algebraMapSubmonoid 
C A⁰) L
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `Module.Finite.of_isLocalization`：of_isLocalization (R S) {Rₚ Sₚ : Type*}
 [CommSemiring R] [CommSemiring S] [CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra 
R S] [Algebra R Rₚ] […
· 使用引理 `Algebra.map_intTraceAux`：Algebra.map_intTraceAux [IsIntegrallyClosed A] 
(x : B) : algebraMap A K (Algebra.intTraceAux A K L B x) = Algebra.trace K L (al
gebraMap B L …
-/
lemma Algebra.algebraMap_intTrace_fractionRing (x : B) :
    algebraMap A (FractionRing A) (Algebra.intTrace A B x) =
      Algebra.trace (FractionRing A) (FractionRing B) (algebraMap B _ x) := by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  exact Algebra.map_intTraceAux x

variable (A B)
/-
**Algebra.intTrace_eq_trace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.intTrace_eq_trace [Module.Free A B] : Algebra.intTrace A B = Algeb
ra.trace A B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `isAlgebraic_of_isFractionRing`：isAlgebraic_of_isFractionRing (R S K L) [
CommRing R] [CommRing S] [Field K] [CommRing L] [Algebra R S] [Algebra R K] [Alg
ebra R L] [Algebra …
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsIntegralClosure.isLocalization`：IsIntegralClosure.isLocalization [IsDo
main A] [Algebra.IsAlgebraic K L] : IsLocalization (Algebra.algebraMapSubmonoid 
C A⁰) L
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.algebraMap_intTrace_fractionRing`：Algebra.algebraMap_intTrace_fr
actionRing (x : B) : algebraMap A (FractionRing A) (Algebra.intTrace A B x) = Al
gebra.trace (FractionRing A) (…
· 使用定理 `Algebra.trace_localization`：Algebra.trace_localization [Module.Free R S]
 [Module.Finite R S] (a : S) : Algebra.trace Rₘ Sₘ (algebraMap S Sₘ a) = algebra
Map R Rₘ (Algebr…
-/
lemma Algebra.intTrace_eq_trace [Module.Free A B] : Algebra.intTrace A B = Algebra.trace A B := by
  ext x
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [Algebra.algebraMap_intTrace_fractionRing, Algebra.trace_localization A A⁰]

open nonZeroDivisors

variable [IsDomain Aₘ] [IsIntegrallyClosed Aₘ] [IsDomain Bₘ] [IsIntegrallyClosed Bₘ]
variable [IsTorsionFree Aₘ Bₘ] [Module.Finite Aₘ Bₘ]

set_option backward.isDefEq.respectTransparency.types false in
include M in
/-
**Algebra.intTrace_eq_of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.intTrace_eq_of_isLocalization (x : B) : algebraMap A Aₘ (Algebra.i
ntTrace A B x) = Algebra.intTrace Aₘ Bₘ (algebraMap B Bₘ x)
参数：x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `isAlgebraic_of_isFractionRing`：isAlgebraic_of_isFractionRing (R S K L) [
CommRing R] [CommRing S] [Field K] [CommRing L] [Algebra R S] [Algebra R K] [Alg
ebra R L] [Algebra …
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsIntegralClosure.isLocalization`：IsIntegralClosure.isLocalization [IsDo
main A] [Algebra.IsAlgebraic K L] : IsLocalization (Algebra.algebraMapSubmonoid 
C A⁰) L
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`：isFractionR
ing_of_isDomain_of_isLocalization [IsDomain R] (S T : Type*) [CommRing S] [CommR
ing T] [Algebra R S] [Algebra R T] [Algebra S T] …
· 使用定理 `Submonoid.monotone_map`：monotone_map {f : F} : Monotone (map f)
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `RingHom.comp_id`：comp_id (f : α ->+* β) : f.comp (id α) = f
· 使用引理 `Module.Finite.of_isLocalization`：of_isLocalization (R S) {Rₚ Sₚ : Type*}
 [CommSemiring R] [CommSemiring S] [CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra 
R S] [Algebra R Rₚ] […
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
（共 32 条，此处仅展示前 30 条）
-/
lemma Algebra.intTrace_eq_of_isLocalization
    (x : B) :
    algebraMap A Aₘ (Algebra.intTrace A B x) = Algebra.intTrace Aₘ Bₘ (algebraMap B Bₘ x) := by
  by_cases hM : 0 ∈ M
  · subsingleton [IsLocalization.uniqueOfZeroMem (S := Aₘ) hM]
  replace hM : M ≤ A⁰ := fun x hx ↦ mem_nonZeroDivisors_iff_ne_zero.mpr (fun e ↦ hM (e ▸ hx))
  let K := FractionRing A
  let L := FractionRing B
  have : IsIntegralClosure B A L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  let f : Aₘ →+* K := IsLocalization.map _ (T := A⁰) (RingHom.id A) hM
  let := f.toAlgebra
  have : IsScalarTower A Aₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Aₘ K
  let g : Bₘ →+* L := IsLocalization.map _
      (M := algebraMapSubmonoid B M) (T := algebraMapSubmonoid B A⁰)
      (RingHom.id B) (Submonoid.monotone_map hM)
  let := g.toAlgebra
  have : IsScalarTower B Bₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower Aₘ K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Aₘ Bₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra (R := Bₘ), RingHom.comp_assoc,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A B Bₘ,
      IsLocalization.map_comp, RingHom.comp_id, ← RingHom.comp_assoc, IsLocalization.map_comp,
      RingHom.comp_id, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (algebraMapSubmonoid B M) Bₘ L
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  have : IsIntegralClosure Bₘ Aₘ L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective Aₘ K
  rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_intTrace_fractionRing,
    Algebra.algebraMap_intTrace (L := L), ← IsScalarTower.algebraMap_apply]

end trace

section norm

variable [IsIntegrallyClosed A]

/-- The restriction of the norm on `L/K` restricted onto `B/A` in an AKLB setup.
See `Algebra.intNorm` instead. -/
noncomputable
/-
**Algebra.intNormAux** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.intNormAux : B ->* A where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Algebra.intNormAux :
    B →* A where
  toFun := fun s ↦ IsIntegralClosure.mk' (R := A) A (Algebra.norm K (algebraMap B L s))
    (isIntegral_norm K <| IsIntegral.map (IsScalarTower.toAlgHom A B L)
      (IsIntegralClosure.isIntegral A L s))
  map_one' := by simp
  map_mul' := fun x y ↦ by simpa using IsIntegralClosure.mk'_mul _ _ _ _ _

variable {A K L B}

omit [FiniteDimensional K L] in
/-
**Algebra.map_intNormAux** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.map_intNormAux (x : B) : algebraMap A K (Algebra.intNormAux A K L 
B x) = Algebra.norm K (algebraMap B L x)
参数：x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.algebraMap_mk'`：algebraMap_mk' (x : B) (hx : IsIntegra
l R x) : algebraMap A B (mk' A x hx) = x
-/
lemma Algebra.map_intNormAux (x : B) :
    algebraMap A K (Algebra.intNormAux A K L B x) = Algebra.norm K (algebraMap B L x) := by
  dsimp [Algebra.intNormAux]
  exact IsIntegralClosure.algebraMap_mk' _ _ _

variable (A B)
variable [IsDomain A] [IsDomain B] [IsIntegrallyClosed B] [Algebra.IsIntegral A B]
  [IsTorsionFree A B]

/-- The norm of a finite extension of integrally closed domains `B/A` is the restriction of
the norm on `Frac(B)/Frac(A)` onto `B/A`. See `Algebra.algebraMap_intNorm`. -/
noncomputable
/-
**Algebra.intNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.intNorm : B ->* A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Algebra.intNorm : B →* A := Algebra.intNormAux A (FractionRing A) (FractionRing B) B

variable {A B}
/-
**Algebra.algebraMap_intNorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.algebraMap_intNorm (x : B) : algebraMap A K (Algebra.intNorm A B x
) = Algebra.norm K (algebraMap B L x)
参数：x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isFractionRing_of_finite_extension`：isFractionRing_of_
finite_extension [IsDomain A] [Algebra K L] [IsScalarTower A K L] [FiniteDimensi
onal K L] : IsFractionRing C L
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `Algebra.intNorm.eq_1`：∀ (A : Type u_1) (B : Type u_6) [inst : CommRing A
] [inst_1 : CommRing B] [inst_2 : Algebra A B]   [inst_3 : IsIntegrallyClosed A]
 [inst_4 :…
· 使用引理 `Algebra.map_intNormAux`：Algebra.map_intNormAux (x : B) : algebraMap A K 
(Algebra.intNormAux A K L B x) = Algebra.norm K (algebraMap B L x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.norm_eq_of_equiv_equiv`：norm_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Ty
pe*} [CommRing A₁] [Ring B₁] [CommRing A₂] [Ring B₂] [Algebra A₁ B₁] [Algebra A₂
 B₂] (e₁ : A₁ ≃+* A₂…
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsFractionRing.algEquiv_commutes`：algEquiv_commutes (e : K₁ ≃ₐ[A] K₂) (f
 : L₁ ≃ₐ[B] L₂) (x : K₁) : algebraMap K₂ L₂ (e x) = f (algebraMap K₁ L₁ x)
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
-/
lemma Algebra.algebraMap_intNorm (x : B) :
    algebraMap A K (Algebra.intNorm A B x) = Algebra.norm K (algebraMap B L x) := by
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply (FractionRing.algEquiv A K).symm.injective
  rw [AlgEquiv.commutes, Algebra.intNorm, Algebra.map_intNormAux,
    ← AlgEquiv.commutes (FractionRing.algEquiv B L)]
  apply Algebra.norm_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv
  ext
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _

@[simp]
/-
**Algebra.algebraMap_intNorm_fractionRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.algebraMap_intNorm_fractionRing (x : B) : algebraMap A (FractionRi
ng A) (Algebra.intNorm A B x) = Algebra.norm (FractionRing A) (algebraMap B (Fra
ctionRing B) x)
参数：x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.map_intNormAux`：Algebra.map_intNormAux (x : B) : algebraMap A K 
(Algebra.intNormAux A K L B x) = Algebra.norm K (algebraMap B L x)
-/
lemma Algebra.algebraMap_intNorm_fractionRing (x : B) :
    algebraMap A (FractionRing A) (Algebra.intNorm A B x) =
      Algebra.norm (FractionRing A) (algebraMap B (FractionRing B) x) :=
  Algebra.map_intNormAux x

variable (A B)
/-
**Algebra.intNorm_intNorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.intNorm_intNorm {C : Type*} [CommRing C] [IsDomain C] [IsIntegrall
yClosed C] [Algebra A C] [Algebra B C] [IsScalarTower A B C] [Algebra.IsIntegral
 A C] [Algebra.IsIntegral B C] [IsTorsionFree A C] [IsTorsionFree B C] (x : C) :
 intNorm A B (intNorm B C x) = intNorm A C x
参数：x : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.algebraMap_intNorm_fractionRing`：Algebra.algebraMap_intNorm_frac
tionRing (x : B) : algebraMap A (FractionRing A) (Algebra.intNorm A B x) = Algeb
ra.norm (FractionRing A) (alg…
· 使用定理 `Algebra.norm_norm`：Algebra.norm_norm {A} [Ring A] [Algebra R A] [Algebra
 S A] [IsScalarTower R S A] [Module.Free S A] {a : A} : norm R (norm S a) = norm
 R a
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `FractionRing.instIsScalarTower_1`：∀ (A : Type u_4) [inst : CommRing A] [
IsDomain A] (k : Type u_6) (K : Type u_7) [inst_2 : Field k] [inst_3 : Field K] 
  [inst_4 : Algebra A …
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
-/
theorem Algebra.intNorm_intNorm {C : Type*} [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    [Algebra A C] [Algebra B C] [IsScalarTower A B C] [Algebra.IsIntegral A C]
    [Algebra.IsIntegral B C] [IsTorsionFree A C] [IsTorsionFree B C] (x : C) :
    intNorm A B (intNorm B C x) = intNorm A C x := by
  apply FaithfulSMul.algebraMap_injective A (FractionRing A)
  rw [algebraMap_intNorm_fractionRing, algebraMap_intNorm_fractionRing,
    algebraMap_intNorm_fractionRing, Algebra.norm_norm]
/-
**Algebra.intNorm_eq_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.intNorm_eq_norm [Module.Free A B] [Module.Finite A B] : Algebra.in
tNorm A B = Algebra.norm A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.algebraMap_intNorm_fractionRing`：Algebra.algebraMap_intNorm_frac
tionRing (x : B) : algebraMap A (FractionRing A) (Algebra.intNorm A B x) = Algeb
ra.norm (FractionRing A) (alg…
· 使用定理 `Algebra.norm_localization`：Algebra.norm_localization [Module.Free R S] [
Module.Finite R S] (a : S) : Algebra.norm Rₘ (algebraMap S Sₘ a) = algebraMap R 
Rₘ (Algebra.nor…
· 使用定理 `Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors
`：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (S' : Type u_5)   [inst_3 : CommRing S'] [F…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
-/
lemma Algebra.intNorm_eq_norm [Module.Free A B] [Module.Finite A B] :
    Algebra.intNorm A B = Algebra.norm A := by
  ext x
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [Algebra.algebraMap_intNorm_fractionRing, Algebra.norm_localization A A⁰]

@[simp]
/-
**Algebra.intNorm_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.intNorm_zero [FiniteDimensional (FractionRing A) (FractionRing B)]
 : Algebra.intNorm A B 0 = 0
参数：FractionRing A；FractionRing B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.algebraMap_intNorm_fractionRing`：Algebra.algebraMap_intNorm_frac
tionRing (x : B) : algebraMap A (FractionRing A) (Algebra.intNorm A B x) = Algeb
ra.norm (FractionRing A) (alg…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Algebra.norm_zero`：norm_zero [Nontrivial S] [Module.Free R S] [Module.Fi
nite R S] : norm R (0 : S) = 0
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Algebra.intNorm_zero [FiniteDimensional (FractionRing A) (FractionRing B)] :
    Algebra.intNorm A B 0 = 0 := by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective A (FractionRing A)
  simp

variable {A B}

attribute [local instance] FractionRing.liftAlgebra

@[simp]
/-
**Algebra.intNorm_map_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.intNorm_map_algEquiv [IsDomain B₂] [IsIntegrallyClosed B₂] [Algebr
a.IsIntegral A B₂] [IsTorsionFree A B₂] [Algebra.IsAlgebraic (FractionRing A) (F
ractionRing B)] [Algebra.IsAlgebraic (FractionRing A) (FractionRing B₂)] (x : B)
 (σ : B ≃ₐ[A] B₂) : Algebra.intNorm A B₂ (σ x) = Algebra.intNorm A B x
参数：FractionRing A；FractionRing B；FractionRing A；FractionRing B₂；x : B；σ : B ≃ₐ[A
] B₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.algebraMap_intNorm_fractionRing`：Algebra.algebraMap_intNorm_frac
tionRing (x : B) : algebraMap A (FractionRing A) (Algebra.intNorm A B x) = Algeb
ra.norm (FractionRing A) (alg…
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `galLiftEquiv_algebraMap_apply`：galLiftEquiv_algebraMap_apply [Algebra.Is
Algebraic K L₂] (σ : B ≃ₐ[A] B₂) (x : B) : galLiftEquiv K L L₂ σ (algebraMap B L
 x) = algebraMap B₂…
· 使用引理 `Algebra.norm_eq_of_algEquiv`：norm_eq_of_algEquiv [Ring T] [Algebra R T] 
(e : S ≃ₐ[R] T) (x) : Algebra.norm R (e x) = Algebra.norm R x
-/
theorem Algebra.intNorm_map_algEquiv [IsDomain B₂] [IsIntegrallyClosed B₂] [Algebra.IsIntegral A B₂]
    [IsTorsionFree A B₂] [Algebra.IsAlgebraic (FractionRing A) (FractionRing B)]
    [Algebra.IsAlgebraic (FractionRing A) (FractionRing B₂)]
    (x : B) (σ : B ≃ₐ[A] B₂) :
    Algebra.intNorm A B₂ (σ x) = Algebra.intNorm A B x := by
  apply FaithfulSMul.algebraMap_injective A (FractionRing A)
  rw [algebraMap_intNorm_fractionRing, algebraMap_intNorm_fractionRing,
    ← galLiftEquiv_algebraMap_apply (FractionRing A) (FractionRing B), norm_eq_of_algEquiv]

@[simp]
/-
**Algebra.intNorm_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.intNorm_eq_zero [FiniteDimensional (FractionRing A) (FractionRing 
B)] {x : B} : Algebra.intNorm A B x = 0 ↔ x = 0
参数：FractionRing A；FractionRing B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Algebra.algebraMap_intNorm_fractionRing`：Algebra.algebraMap_intNorm_frac
tionRing (x : B) : algebraMap A (FractionRing A) (Algebra.intNorm A B x) = Algeb
ra.norm (FractionRing A) (alg…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Algebra.intNorm_eq_zero [FiniteDimensional (FractionRing A) (FractionRing B)] {x : B} :
    Algebra.intNorm A B x = 0 ↔ x = 0 := by
  rw [← (IsFractionRing.injective A (FractionRing A)).eq_iff,
    ← (IsFractionRing.injective B (FractionRing B)).eq_iff]
  simp only [algebraMap_intNorm_fractionRing, map_zero, norm_eq_zero_iff]
/-
**Algebra.intNorm_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.intNorm_ne_zero [FiniteDimensional (FractionRing A) (FractionRing 
B)] {x : B} : Algebra.intNorm A B x != 0 ↔ x != 0
参数：FractionRing A；FractionRing B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Algebra.intNorm_ne_zero [FiniteDimensional (FractionRing A) (FractionRing B)] {x : B} :
    Algebra.intNorm A B x ≠ 0 ↔ x ≠ 0 := by simp

variable [IsDomain Aₘ] [IsIntegrallyClosed Aₘ] [IsDomain Bₘ] [IsIntegrallyClosed Bₘ]
variable [IsTorsionFree Aₘ Bₘ] [Algebra.IsIntegral Aₘ Bₘ]

set_option backward.isDefEq.respectTransparency.types false in
include M in
/-
**Algebra.intNorm_eq_of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.intNorm_eq_of_isLocalization [FiniteDimensional (FractionRing A) (
FractionRing B)] (x : B) : algebraMap A Aₘ (Algebra.intNorm A B x) = Algebra.int
Norm Aₘ Bₘ (algebraMap B Bₘ x)
参数：FractionRing A；FractionRing B；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`：isFractionR
ing_of_isDomain_of_isLocalization [IsDomain R] (S T : Type*) [CommRing S] [CommR
ing T] [Algebra R S] [Algebra R T] [Algebra S T] …
· 使用定理 `Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors
`：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (S' : Type u_5)   [inst_3 : CommRing S'] [F…
· 使用定理 `Submonoid.monotone_map`：monotone_map {f : F} : Monotone (map f)
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `RingHom.comp_id`：comp_id (f : α ->+* β) : f.comp (id α) = f
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用引理 `Algebra.algebraMap_intNorm_fractionRing`：Algebra.algebraMap_intNorm_frac
tionRing (x : B) : algebraMap A (FractionRing A) (Algebra.intNorm A B x) = Algeb
ra.norm (FractionRing A) (alg…
· 使用引理 `Algebra.algebraMap_intNorm`：Algebra.algebraMap_intNorm (x : B) : algebra
Map A K (Algebra.intNorm A B x) = Algebra.norm K (algebraMap B L x)
-/
lemma Algebra.intNorm_eq_of_isLocalization [FiniteDimensional (FractionRing A) (FractionRing B)]
    (x : B) :
    algebraMap A Aₘ (Algebra.intNorm A B x) = Algebra.intNorm Aₘ Bₘ (algebraMap B Bₘ x) := by
  by_cases hM : 0 ∈ M
  · subsingleton [IsLocalization.uniqueOfZeroMem (S := Aₘ) hM]
  replace hM : M ≤ A⁰ := fun x hx ↦ mem_nonZeroDivisors_iff_ne_zero.mpr (fun e ↦ hM (e ▸ hx))
  let K := FractionRing A
  let L := FractionRing B
  let f : Aₘ →+* K := IsLocalization.map _ (T := A⁰) (RingHom.id A) hM
  let := f.toAlgebra
  have : IsScalarTower A Aₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Aₘ K
  let g : Bₘ →+* L := IsLocalization.map _
      (M := algebraMapSubmonoid B M) (T := algebraMapSubmonoid B A⁰)
      (RingHom.id B) (Submonoid.monotone_map hM)
  let := g.toAlgebra
  have : IsScalarTower B Bₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower Aₘ K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Aₘ Bₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra (R := Bₘ), RingHom.comp_assoc,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A B Bₘ,
      IsLocalization.map_comp, RingHom.comp_id, ← RingHom.comp_assoc, IsLocalization.map_comp,
      RingHom.comp_id, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (algebraMapSubmonoid B M) Bₘ L
  have : IsIntegralClosure Bₘ Aₘ L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective Aₘ K
  rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_intNorm_fractionRing,
    Algebra.algebraMap_intNorm (L := L), ← IsScalarTower.algebraMap_apply]

end norm

variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]
  [Module.Finite A B] [IsTorsionFree A B]

/-
**Algebra.algebraMap_intNorm_of_isGalois** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.algebraMap_intNorm_of_isGalois [IsGalois (FractionRing A) (Fractio
nRing B)] {x : B} : algebraMap A B (Algebra.intNorm A B x) = ∏ σ : B ≃ₐ[A] B, σ 
x
参数：FractionRing A；FractionRing B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `Module.Finite.of_isLocalization`：of_isLocalization (R S) {Rₚ Sₚ : Type*}
 [CommSemiring R] [CommSemiring S] [CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra 
R S] [Algebra R Rₚ] […
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors
`：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (S' : Type u_5)   [inst_3 : CommRing S'] [F…
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `IsPurelyInseparable.isIntegral`：∀ {F : Type u_1} {E : Type u_2} {inst : 
CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInseparab
le F E], Algebra.IsI…
· 使用定理 `Algebra.isIntegral_norm`：isIntegral_norm [Algebra R L] [Algebra R K] [Is
ScalarTower R K L] {x : L} (hx : IsIntegral R x) : IsIntegral R (norm K x)
· 使用定理 `IsIntegral.algebraMap`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra R 
A] [inst_4 …
· 使用定理 `IsIntegralClosure.isIntegral`：∀ (R : Type u_1) {A : Type u_2} (B : Type 
u_3) [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : CommRing B]   [inst_3 :
 Algebra R B] [ins…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `prod_galRestrict_eq_norm`：prod_galRestrict_eq_norm [IsGalois K L] [IsInt
egrallyClosed A] (x : B) : (∏ σ : Gal(L/K), galRestrict A K L B σ x) = algebraMa
p A B (IsInteg…
-/
lemma Algebra.algebraMap_intNorm_of_isGalois [IsGalois (FractionRing A) (FractionRing B)] {x : B} :
    algebraMap A B (Algebra.intNorm A B x) = ∏ σ : B ≃ₐ[A] B, σ x := by
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  rw [← (galRestrict A (FractionRing A) (FractionRing B) B).toEquiv.prod_comp]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  convert! (prod_galRestrict_eq_norm A (FractionRing A) (FractionRing B) B x).symm

open Polynomial IsScalarTower in
/-
**Algebra.dvd_algebraMap_intNorm_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.dvd_algebraMap_intNorm_self (x : B) : x ∣ algebraMap A B (intNorm 
A B x)
参数：x : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `Module.Finite.of_isLocalization`：of_isLocalization (R S) {Rₚ Sₚ : Type*}
 [CommSemiring R] [CommSemiring S] [CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra 
R S] [Algebra R Rₚ] […
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors
`：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (S' : Type u_5)   [inst_3 : CommRing S'] [F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.intNorm_zero`：Algebra.intNorm_zero [FiniteDimensional (FractionR
ing A) (FractionRing B)] : Algebra.intNorm A B 0 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsScalarTower.coe_toAlgHom'`：coe_toAlgHom' : (toAlgHom R S A : S -> A) =
 algebraMap S A
（共 78 条，此处仅展示前 30 条）
-/
theorem Algebra.dvd_algebraMap_intNorm_self (x : B) : x ∣ algebraMap A B (intNorm A B x) := by
  classical
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  by_cases hx : x = 0
  · exact ⟨1, by simp [hx]⟩
  let K := FractionRing A
  let L := FractionRing B
  let E := AlgebraicClosure L
  suffices IsIntegral A ((algebraMap B L x)⁻¹ * (algebraMap A L (intNorm A B x))) by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp <|
      _root_.IsIntegral.tower_top (A := B) this
    refine ⟨y, ?_⟩
    apply FaithfulSMul.algebraMap_injective B L
    rw [← algebraMap_apply, map_mul, hy, mul_inv_cancel_left₀]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B L)).mpr hx
  rw [← isIntegral_algHom_iff (toAlgHom A L E)
    (FaithfulSMul.algebraMap_injective L E), coe_toAlgHom', map_mul, map_inv₀,
    algebraMap_apply A K L, algebraMap_intNorm (L := L), ← algebraMap_apply, ← algebraMap_apply,
    norm_eq_prod_roots _ (IsAlgClosed.splits _), ← Multiset.prod_erase
    (a := algebraMap B E x)]
  · have := IsTorsionFree.trans_faithfulSMul B L E
    rw [mul_pow, ← mul_pow_sub_one (Nat.pos_iff_ne_zero.1 Module.finrank_pos) (algebraMap B E x),
      mul_assoc, inv_mul_cancel_left₀]
    · refine IsIntegral.mul (IsIntegral.pow ?_ _)
        (IsIntegral.pow (IsIntegral.multiset_prod (fun a ha ↦ ⟨minpoly A x, minpoly.monic
          (IsIntegral.isIntegral x), ?_⟩)) _)
      · exact (isIntegral_algebraMap_iff (isTorsionFree_iff_algebraMap_injective.1 this)).mpr
          (IsIntegral.isIntegral x)
      · replace ha := Multiset.erase_subset _ _ ha
        suffices (aeval a) ((minpoly A x).map (algebraMap A K)) = 0 by simpa
        rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L (IsIntegral.isIntegral x)]
        simp only [mem_roots', ne_eq, Polynomial.map_eq_zero, IsRoot.def, eval_map_algebraMap] at ha
        exact ha.2
    · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B E)).mpr hx
  · simp only [mem_roots', ne_eq, Polynomial.map_eq_zero, IsRoot.def, eval_map_algebraMap]
    refine ⟨minpoly.ne_zero (IsIntegral.isIntegral _), ?_⟩
    simp [algebraMap_apply B L E, aeval_algebraMap_apply]
