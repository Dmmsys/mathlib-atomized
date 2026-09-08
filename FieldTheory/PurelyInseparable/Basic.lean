/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.FieldTheory.IsSepClosed

/-!

# Basic results about purely inseparable extensions

This file contains basic definitions and results about purely inseparable extensions.

## Main definitions

- `IsPurelyInseparable`: typeclass for purely inseparable field extensions: an algebraic extension
  `E / F` is purely inseparable if and only if the minimal polynomial of every element of `E ∖ F`
  is not separable.

## Main results

- `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`,
  `IsPurelyInseparable.bijective_algebraMap_of_isSeparable`,
  `IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable`:
  if `E / F` is both purely inseparable and separable, then `algebraMap F E` is surjective
  (hence bijective). In particular, if an intermediate field of `E / F` is both purely inseparable
  and separable, then it is equal to `F`.

- `isPurelyInseparable_iff_pow_mem`: a field extension `E / F` of exponential characteristic `q` is
  purely inseparable if and only if for every element `x` of `E`, there exists a natural number `n`
  such that `x ^ (q ^ n)` is contained in `F`.

- `IsPurelyInseparable.trans`: if `E / F` and `K / E` are both purely inseparable extensions, then
  `K / F` is also purely inseparable.

- `isPurelyInseparable_iff_natSepDegree_eq_one`: `E / F` is purely inseparable if and only if for
  every element `x` of `E`, its minimal polynomial has separable degree one.

- `isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C`: a field extension `E / F` of exponential
  characteristic `q` is purely inseparable if and only if for every element `x` of `E`, the minimal
  polynomial of `x` over `F` is of form `X ^ (q ^ n) - y` for some natural number `n` and some
  element `y` of `F`.

- `isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow`: a field extension `E / F` of exponential
  characteristic `q` is purely inseparable if and only if for every element `x` of `E`, the minimal
  polynomial of `x` over `F` is of form `(X - x) ^ (q ^ n)` for some natural number `n`.

- `isPurelyInseparable_iff_finSepDegree_eq_one`: an extension is purely inseparable
  if and only if it has finite separable degree (`Field.finSepDegree`) one.

- `IsPurelyInseparable.normal`: a purely inseparable extension is normal.

- `separableClosure.isPurelyInseparable`: if `E / F` is algebraic, then `E` is purely inseparable
  over the separable closure of `F` in `E`.

- `separableClosure_le_iff`: if `E / F` is algebraic, then an intermediate field of `E / F` contains
  the separable closure of `F` in `E` if and only if `E` is purely inseparable over it.

- `eq_separableClosure_iff`: if `E / F` is algebraic, then an intermediate field of `E / F` is equal
  to the separable closure of `F` in `E` if and only if it is separable over `F`, and `E`
  is purely inseparable over it.

- `IsPurelyInseparable.injective_comp_algebraMap`: if `E / F` is purely inseparable, then for any
  reduced ring `L`, the map `(E →+* L) → (F →+* L)` induced by `algebraMap F E` is injective.
  In particular, a purely inseparable field extension is an epimorphism in the category of fields.

- `IsPurelyInseparable.of_injective_comp_algebraMap`: if `L` is an algebraically closed field
  containing `E`, such that the map `(E →+* L) → (F →+* L)` induced by `algebraMap F E` is
  injective, then `E / F` is purely inseparable. As a corollary, epimorphisms in the category of
  fields must be purely inseparable extensions.

- `Field.finSepDegree_eq`: if `E / F` is algebraic, then the `Field.finSepDegree F E` is equal to
  `Field.sepDegree F E` as a natural number. This means that the cardinality of `Field.Emb F E`
  and the degree of `(separableClosure F E) / F` are both finite or infinite, and when they are
  finite, they coincide.

- `Field.finSepDegree_mul_finInsepDegree`: the finite separable degree multiply by the finite
  inseparable degree is equal to the (finite) field extension degree.

## Tags

separable degree, degree, separable closure, purely inseparable

-/

@[expose] public section

open Module Polynomial IntermediateField Field

noncomputable section

universe u v w

section General

variable (F E : Type*) [CommRing F] [Ring E] [Algebra F E]
variable (K : Type*) [Ring K] [Algebra F K]

/-- Typeclass for purely inseparable field extensions: an algebraic extension `E / F` is purely
inseparable if and only if the minimal polynomial of every element of `E ∖ F` is not separable.

We define this for general (commutative) rings and only assume `F` and `E` are fields
if this is needed for a proof. -/
/-
**IsPurelyInseparable** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (E : Type u_2) → [inst : CommRing F] → [inst_1 : Ring E] 
→ [Algebra F E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for purely inseparable field extensions: an algebraic extension `E / F
` is purely
inseparable if and only if the minimal polynomial of every element of `E ∖ F` is
 not separable.

We define this for general (commutative) rings and only assume `F` and `E` are f
ields
if this is needed for a proof.
-/
class IsPurelyInseparable : Prop where
  isIntegral : Algebra.IsIntegral F E
  inseparable' (x : E) : IsSeparable F x → x ∈ (algebraMap F E).range

attribute [instance] IsPurelyInseparable.isIntegral

variable {E} in
/-
**IsPurelyInseparable.isIntegral'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.isIntegral' [IsPurelyInseparable F E] (x : E) : IsInte
gral F x
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `IsPurelyInseparable.isIntegral`：∀ {F : Type u_1} {E : Type u_2} {inst : 
CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInseparab
le F E], Algebra.IsI…
-/
theorem IsPurelyInseparable.isIntegral' [IsPurelyInseparable F E] (x : E) : IsIntegral F x :=
  Algebra.IsIntegral.isIntegral _
/-
**IsPurelyInseparable.isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.isAlgebraic [Nontrivial F] [IsPurelyInseparable F E] :
 Algebra.IsAlgebraic F E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.isIntegral`：∀ {F : Type u_1} {E : Type u_2} {inst : 
CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInseparab
le F E], Algebra.IsI…
-/
theorem IsPurelyInseparable.isAlgebraic [Nontrivial F] [IsPurelyInseparable F E] :
    Algebra.IsAlgebraic F E := inferInstance

variable {E}
/-
**IsPurelyInseparable.inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.inseparable [IsPurelyInseparable F E] : forall x : E, 
IsSeparable F x -> x in (algebraMap F E).range
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.inseparable'`：∀ {F : Type u_1} {E : Type u_2} {inst 
: CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInsepar
able F E] (x : E), IsS…
-/
theorem IsPurelyInseparable.inseparable [IsPurelyInseparable F E] :
    ∀ x : E, IsSeparable F x → x ∈ (algebraMap F E).range :=
  IsPurelyInseparable.inseparable'

variable {F}
/-
**isPurelyInseparable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPurelyInseparable_iff : IsPurelyInseparable F E ↔ forall x : E, IsIntegr
al F x ∧ (IsSeparable F x -> x in (algebraMap F E).range)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.isIntegral'`：IsPurelyInseparable.isIntegral' [IsPure
lyInseparable F E] (x : E) : IsIntegral F x
· 使用定理 `IsPurelyInseparable.inseparable'`：∀ {F : Type u_1} {E : Type u_2} {inst 
: CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInsepar
able F E] (x : E), IsS…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isPurelyInseparable_iff : IsPurelyInseparable F E ↔ ∀ x : E,
    IsIntegral F x ∧ (IsSeparable F x → x ∈ (algebraMap F E).range) :=
  ⟨fun h x ↦ ⟨h.isIntegral' _ x, h.inseparable' x⟩, fun h ↦ ⟨⟨fun x ↦ (h x).1⟩, fun x ↦ (h x).2⟩⟩

variable {K}

/-- Transfer `IsPurelyInseparable` across an `AlgEquiv`. -/
/-
**AlgEquiv.isPurelyInseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.isPurelyInseparable (e : K ≃ₐ[F] E) [IsPurelyInseparable F K] : I
sPurelyInseparable F E
参数：e : K ≃ₐ[F] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isIntegral_algEquiv`：isIntegral_algEquiv {A B : Type*} [Ring A] [Ring B]
 [Algebra R A] [Algebra R B] (f : A ≃ₐ[R] B) {x : A} : IsIntegral R (f x) ↔ IsIn
tegral R …
· 使用定理 `IsPurelyInseparable.isIntegral'`：IsPurelyInseparable.isIntegral' [IsPure
lyInseparable F E] (x : E) : IsIntegral F x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsPurelyInseparable.inseparable`：IsPurelyInseparable.inseparable [IsPure
lyInseparable F E] : forall x : E, IsSeparable F x -> x in (algebraMap F E).rang
e
· 使用定理 `minpoly.algEquiv_eq`：algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f
 x) = minpoly A x
· 使用定理 `IsSeparable.eq_1`：∀ (F : Type u_1) {K : Type u_3} [inst : CommRing F] [i
nst_1 : Ring K] [inst_2 : Algebra F K] (x : K),   IsSeparable F x = (minpoly F x
).Sepa…

--- 原说明 ---
Transfer `IsPurelyInseparable` across an `AlgEquiv`.
-/
theorem AlgEquiv.isPurelyInseparable (e : K ≃ₐ[F] E) [IsPurelyInseparable F K] :
    IsPurelyInseparable F E := by
  refine ⟨⟨fun _ ↦ by rw [← isIntegral_algEquiv e.symm]; exact IsPurelyInseparable.isIntegral' F _⟩,
    fun x h ↦ ?_⟩
  rw [IsSeparable, ← minpoly.algEquiv_eq e.symm] at h
  simpa only [RingHom.mem_range, algebraMap_eq_apply] using IsPurelyInseparable.inseparable F _ h
/-
**AlgEquiv.isPurelyInseparable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.isPurelyInseparable_iff (e : K ≃ₐ[F] E) : IsPurelyInseparable F K
 ↔ IsPurelyInseparable F E
参数：e : K ≃ₐ[F] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.isPurelyInseparable`：AlgEquiv.isPurelyInseparable (e : K ≃ₐ[F] 
E) [IsPurelyInseparable F K] : IsPurelyInseparable F E
-/
theorem AlgEquiv.isPurelyInseparable_iff (e : K ≃ₐ[F] E) :
    IsPurelyInseparable F K ↔ IsPurelyInseparable F E :=
  ⟨fun _ ↦ e.isPurelyInseparable, fun _ ↦ e.symm.isPurelyInseparable⟩

/-- If `E / F` is an algebraic extension, `F` is separably closed,
then `E / F` is purely inseparable. -/
/-
**Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed** 是 Mathlib 中的一个实例，位于命名
空间 ``。
形式化陈述：Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed {F : Type u} {E : T
ype v} [Field F] [Ring E] [IsDomain E] [Algebra F E] [Algebra.IsAlgebraic F E] [
IsSepClosed F] : IsPurelyInseparable F E
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `minpoly.mem_range_of_degree_eq_one`：mem_range_of_degree_eq_one (hx : (mi
npoly A x).degree = 1) : x in (algebraMap A B).range
· 使用定理 `IsSepClosed.degree_eq_one_of_irreducible`：degree_eq_one_of_irreducible [
IsSepClosed k] {p : k[X]} (hp : Irreducible p) (hsep : p.Separable) : p.degree =
 1
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…

--- 原说明 ---
If `E / F` is an algebraic extension, `F` is separably closed,
then `E / F` is purely inseparable.
-/
instance Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
    {F : Type u} {E : Type v} [Field F] [Ring E] [IsDomain E] [Algebra F E]
    [Algebra.IsAlgebraic F E] [IsSepClosed F] : IsPurelyInseparable F E :=
  ⟨inferInstance, fun x h ↦ minpoly.mem_range_of_degree_eq_one F x <|
    IsSepClosed.degree_eq_one_of_irreducible F (minpoly.irreducible
      (Algebra.IsIntegral.isIntegral _)) h⟩

variable (F E K)

/-- If `E / F` is both purely inseparable and separable, then `algebraMap F E` is surjective. -/
/-
**IsPurelyInseparable.surjective_algebraMap_of_isSeparable** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：IsPurelyInseparable.surjective_algebraMap_of_isSeparable [IsPurelyInsepara
ble F E] [Algebra.IsSeparable F E] : Function.Surjective (algebraMap F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.inseparable`：IsPurelyInseparable.inseparable [IsPure
lyInseparable F E] : forall x : E, IsSeparable F x -> x in (algebraMap F E).rang
e
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x

--- 原说明 ---
If `E / F` is both purely inseparable and separable, then `algebraMap F E` is su
rjective.
-/
theorem IsPurelyInseparable.surjective_algebraMap_of_isSeparable
    [IsPurelyInseparable F E] [Algebra.IsSeparable F E] : Function.Surjective (algebraMap F E) :=
  fun x ↦ IsPurelyInseparable.inseparable F x (Algebra.IsSeparable.isSeparable F x)

/-- If `E / F` is both purely inseparable and separable, then `algebraMap F E` is bijective. -/
/-
**IsPurelyInseparable.bijective_algebraMap_of_isSeparable** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：IsPurelyInseparable.bijective_algebraMap_of_isSeparable [Nontrivial E] [Is
Domain F] [IsTorsionFree F E] [IsPurelyInseparable F E] [Algebra.IsSeparable F E
] : Function.Bijective (algebraMap F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`：IsPurelyInsepa
rable.surjective_algebraMap_of_isSeparable [IsPurelyInseparable F E] [Algebra.Is
Separable F E] : Function.Surjective (algebraM…

--- 原说明 ---
If `E / F` is both purely inseparable and separable, then `algebraMap F E` is bi
jective.
-/
theorem IsPurelyInseparable.bijective_algebraMap_of_isSeparable
    [Nontrivial E] [IsDomain F] [IsTorsionFree F E]
    [IsPurelyInseparable F E] [Algebra.IsSeparable F E] : Function.Bijective (algebraMap F E) :=
  ⟨FaithfulSMul.algebraMap_injective F E, surjective_algebraMap_of_isSeparable F E⟩

variable {F E} in
/-- If a subalgebra of `E / F` is both purely inseparable and separable, then it is equal
to `F`. -/
/-
**Subalgebra.eq_bot_of_isPurelyInseparable_of_isSeparable** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：Subalgebra.eq_bot_of_isPurelyInseparable_of_isSeparable (L : Subalgebra F 
E) [IsPurelyInseparable F L] [Algebra.IsSeparable F L] : L = ⊥
参数：L : Subalgebra F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`：IsPurelyInsepa
rable.surjective_algebraMap_of_isSeparable [IsPurelyInseparable F E] [Algebra.Is
Separable F E] : Function.Surjective (algebraM…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If a subalgebra of `E / F` is both purely inseparable and separable, then it is 
equal
to `F`.
-/
theorem Subalgebra.eq_bot_of_isPurelyInseparable_of_isSeparable (L : Subalgebra F E)
    [IsPurelyInseparable F L] [Algebra.IsSeparable F L] : L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (Subalgebra.val _) hy⟩

/-- If an intermediate field of `E / F` is both purely inseparable and separable, then it is equal
to `F`. -/
/-
**IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable {F : Type u
} {E : Type v} [Field F] [Field E] [Algebra F E] (L : IntermediateField F E) [Is
PurelyInseparable F L] [Algebra.IsSeparable F L] : L = ⊥
参数：L : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`：IsPurelyInsepa
rable.surjective_algebraMap_of_isSeparable [IsPurelyInseparable F E] [Algebra.Is
Separable F E] : Function.Surjective (algebraM…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
If an intermediate field of `E / F` is both purely inseparable and separable, th
en it is equal
to `F`.
-/
theorem IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] (L : IntermediateField F E)
    [IsPurelyInseparable F L] [Algebra.IsSeparable F L] : L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L E) hy⟩

/-- If `E / F` is purely inseparable, then the separable closure of `F` in `E` is
equal to `F`. -/
/-
**separableClosure.eq_bot_of_isPurelyInseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separableClosure.eq_bot_of_isPurelyInseparable (F : Type u) (E : Type v) [
Field F] [Field E] [Algebra F E] [IsPurelyInseparable F E] : separableClosure F 
E = ⊥
参数：F : Type u；E : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `IsPurelyInseparable.inseparable`：IsPurelyInseparable.inseparable [IsPure
lyInseparable F E] : forall x : E, IsSeparable F x -> x in (algebraMap F E).rang
e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_separableClosure_iff`：mem_separableClosure_iff {x : E} : x in separa
bleClosure F E ↔ IsSeparable F x

--- 原说明 ---
If `E / F` is purely inseparable, then the separable closure of `F` in `E` is
equal to `F`.
-/
theorem separableClosure.eq_bot_of_isPurelyInseparable
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [IsPurelyInseparable F E] :
    separableClosure F E = ⊥ :=
  bot_unique fun x h ↦ IsPurelyInseparable.inseparable F x (mem_separableClosure_iff.1 h)

/-- If `E / F` is an algebraic extension, then the separable closure of `F` in `E` is
equal to `F` if and only if `E / F` is purely inseparable. -/
/-
**separableClosure.eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separableClosure.eq_bot_iff {F : Type u} {E : Type v} [Field F] [Field E] 
[Algebra F E] [Algebra.IsAlgebraic F E] : separableClosure F E = ⊥ ↔ IsPurelyIns
eparable F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isPurelyInseparable_iff`：isPurelyInseparable_iff : IsPurelyInseparable F
 E ↔ forall x : E, IsIntegral F x ∧ (IsSeparable F x -> x in (algebraMap F E).ra
nge)
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_separableClosure_iff`：mem_separableClosure_iff {x : E} : x in separa
bleClosure F E ↔ IsSeparable F x
· 使用定理 `separableClosure.eq_bot_of_isPurelyInseparable`：separableClosure.eq_bot_
of_isPurelyInseparable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F 
E] [IsPurelyInseparable F E] : separ…

--- 原说明 ---
If `E / F` is an algebraic extension, then the separable closure of `F` in `E` i
s
equal to `F` if and only if `E / F` is purely inseparable.
-/
theorem separableClosure.eq_bot_iff
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E] :
    separableClosure F E = ⊥ ↔ IsPurelyInseparable F E :=
  ⟨fun h ↦ isPurelyInseparable_iff.2 fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, fun hs ↦ by
    simpa only [h] using! mem_separableClosure_iff.2 hs⟩, fun _ ↦ eq_bot_of_isPurelyInseparable F E⟩
/-
**isPurelyInseparable_self** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isPurelyInseparable_self : IsPurelyInseparable F F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isPurelyInseparable_self : IsPurelyInseparable F F :=
  ⟨inferInstance, fun x _ ↦ ⟨x, rfl⟩⟩

section

variable (F : Type u) {E : Type v} [Field F] [Ring E] [IsDomain E] [Algebra F E]
variable (q : ℕ) [ExpChar F q] (x : E)

/-- A field extension `E / F` of exponential characteristic `q` is purely inseparable
if and only if for every element `x` of `E`, there exists a natural number `n` such that
`x ^ (q ^ n)` is contained in `F`. -/
@[stacks 09HE]
/-
**isPurelyInseparable_iff_pow_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPurelyInseparable_iff_pow_mem : IsPurelyInseparable F E ↔ forall x : E, 
exists n : Nat, x ^ q ^ n in (algebraMap F E).range
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPurelyInseparable_iff`：isPurelyInseparable_iff : IsPurelyInseparable F
 E ↔ forall x : E, IsIntegral F x ∧ (IsSeparable F x -> x in (algebraMap F E).ra
nge)
· 使用定理 `Irreducible.hasSeparableContraction`：∀ {F : Type u_1} [inst : Field F] (
q : ℕ) [hF : ExpChar F q] {f : Polynomial F},   Irreducible f → Polynomial.HasSe
parableContraction q f
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.Separable.of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {f g
 : Polynomial R}, f.Separable → g ∣ f → g.Separable
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.expand_aeval`：expand_aeval {A : Type*} [Semiring A] [Algebra 
R A] (p : Nat) (P : R[X]) (r : A) : aeval r (expand R p P) = aeval (r ^ p) P
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `minpoly.natSepDegree_eq_one_iff_pow_mem`：natSepDegree_eq_one_iff_pow_mem
 : (minpoly F x).natSepDegree = 1 ↔ exists n : Nat, x ^ q ^ n in (algebraMap F E
).range
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `minpoly.eq_zero`：eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0
· 使用定理 `Polynomial.natSepDegree_zero`：natSepDegree_zero : (0 : F[X]).natSepDegre
e = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `minpoly.natDegree_eq_one_iff`：natDegree_eq_one_iff : (minpoly A x).natDe
gree = 1 ↔ x in (algebraMap A B).range
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.Separable.natSepDegree_eq_natDegree`：∀ {F : Type u} [inst : F
ield F] {f : Polynomial F}, f.Separable → f.natSepDegree = f.natDegree

--- 原说明 ---
A field extension `E / F` of exponential characteristic `q` is purely inseparabl
e
if and only if for every element `x` of `E`, there exists a natural number `n` s
uch that
`x ^ (q ^ n)` is contained in `F`.
-/
theorem isPurelyInseparable_iff_pow_mem :
    IsPurelyInseparable F E ↔ ∀ x : E, ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  rw [isPurelyInseparable_iff]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨g, h1, n, h2⟩ := (minpoly.irreducible (h x).1).hasSeparableContraction q
    exact ⟨n, (h _).2 <| h1.of_dvd <| minpoly.dvd F _ <| by
      simpa only [expand_aeval, minpoly.aeval] using congr_arg (aeval x) h2⟩
  have hdeg := (minpoly.natSepDegree_eq_one_iff_pow_mem q).2 (h x)
  have halg : IsIntegral F x := by_contra fun h' ↦ by
    simp only [minpoly.eq_zero h', natSepDegree_zero, zero_ne_one] at hdeg
  refine ⟨halg, fun hsep ↦ ?_⟩
  rwa [hsep.natSepDegree_eq_natDegree, minpoly.natDegree_eq_one_iff] at hdeg
/-
**IsPurelyInseparable.pow_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.pow_mem [IsPurelyInseparable F E] : exists n : Nat, x 
^ q ^ n in (algebraMap F E).range
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPurelyInseparable_iff_pow_mem`：isPurelyInseparable_iff_pow_mem : IsPur
elyInseparable F E ↔ forall x : E, exists n : Nat, x ^ q ^ n in (algebraMap F E)
.range
-/
theorem IsPurelyInseparable.pow_mem [IsPurelyInseparable F E] :
    ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range :=
  (isPurelyInseparable_iff_pow_mem F q).1 ‹_› x

end

end General

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

section Field

/-- If `K / E / F` is a field extension tower such that `K / F` is purely inseparable,
then `E / F` is also purely inseparable. -/
/-
**IsPurelyInseparable.tower_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.tower_bot [Algebra E K] [IsScalarTower F E K] [IsPurel
yInseparable F K] : IsPurelyInseparable F E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.tower_bot_of_field`：IsIntegral.tower_bot_of_field {R A B : Ty
pe*} [CommRing R] [Field A] [Ring B] [Nontrivial B] [Algebra R A] [Algebra A B] 
[Algebra R B] [IsSc…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsPurelyInseparable.isIntegral'`：IsPurelyInseparable.isIntegral' [IsPure
lyInseparable F E] (x : E) : IsIntegral F x
· 使用定理 `IsPurelyInseparable.inseparable`：IsPurelyInseparable.inseparable [IsPure
lyInseparable F E] : forall x : E, IsSeparable F x -> x in (algebraMap F E).rang
e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.algebraMap_eq`：algebraMap_eq {B} [CommRing B] [Algebra A B] [Alg
ebra B B'] [IsScalarTower A B B'] (h : Function.Injective (algebraMap B B')) (x 
: B) : minp…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsSeparable.eq_1`：∀ (F : Type u_1) {K : Type u_3} [inst : CommRing F] [i
nst_1 : Ring K] [inst_2 : Algebra F K] (x : K),   IsSeparable F x = (minpoly F x
).Sepa…
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)

--- 原说明 ---
If `K / E / F` is a field extension tower such that `K / F` is purely inseparabl
e,
then `E / F` is also purely inseparable.
-/
theorem IsPurelyInseparable.tower_bot [Algebra E K] [IsScalarTower F E K]
    [IsPurelyInseparable F K] : IsPurelyInseparable F E := by
  refine ⟨⟨fun x ↦ (isIntegral' F (algebraMap E K x)).tower_bot_of_field⟩, fun x h ↦ ?_⟩
  rw [IsSeparable, ← minpoly.algebraMap_eq (algebraMap E K).injective] at h
  obtain ⟨y, h⟩ := inseparable F _ h
  exact ⟨y, (algebraMap E K).injective (h.symm ▸ (IsScalarTower.algebraMap_apply F E K y).symm)⟩

/-- If `K / E / F` is a field extension tower such that `K / F` is purely inseparable,
then `K / E` is also purely inseparable. -/
/-
**IsPurelyInseparable.tower_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.tower_top [Algebra E K] [IsScalarTower F E K] [h : IsP
urelyInseparable F K] : IsPurelyInseparable E K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpChar.exists`：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar
 R q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `expChar_of_injective_algebraMap`：expChar_of_injective_algebraMap [CommSe
miring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (
q : Nat) [ExpChar R q…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPurelyInseparable_iff_pow_mem`：isPurelyInseparable_iff_pow_mem : IsPur
elyInseparable F E ↔ forall x : E, exists n : Nat, x ^ q ^ n in (algebraMap F E)
.range
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)

--- 原说明 ---
If `K / E / F` is a field extension tower such that `K / F` is purely inseparabl
e,
then `K / E` is also purely inseparable.
-/
theorem IsPurelyInseparable.tower_top [Algebra E K] [IsScalarTower F E K]
    [h : IsPurelyInseparable F K] : IsPurelyInseparable E K := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_pow_mem _ q] at h ⊢
  intro x
  obtain ⟨n, y, h⟩ := h x
  exact ⟨n, (algebraMap F E) y, h.symm ▸ (IsScalarTower.algebraMap_apply F E K y).symm⟩

/-- If `E / F` and `K / E` are both purely inseparable extensions, then `K / F` is also
purely inseparable. -/
@[stacks 02JJ "See also 00GM"]
/-
**IsPurelyInseparable.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.trans [Algebra E K] [IsScalarTower F E K] [h1 : IsPure
lyInseparable F E] [h2 : IsPurelyInseparable E K] : IsPurelyInseparable F K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpChar.exists`：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar
 R q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `expChar_of_injective_algebraMap`：expChar_of_injective_algebraMap [CommSe
miring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (
q : Nat) [ExpChar R q…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPurelyInseparable_iff_pow_mem`：isPurelyInseparable_iff_pow_mem : IsPur
elyInseparable F E ↔ forall x : E, exists n : Nat, x ^ q ^ n in (algebraMap F E)
.range
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d

--- 原说明 ---
If `E / F` and `K / E` are both purely inseparable extensions, then `K / F` is a
lso
purely inseparable.
-/
theorem IsPurelyInseparable.trans [Algebra E K] [IsScalarTower F E K]
    [h1 : IsPurelyInseparable F E] [h2 : IsPurelyInseparable E K] : IsPurelyInseparable F K := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_pow_mem _ q] at h1 h2 ⊢
  intro x
  obtain ⟨n, y, h2⟩ := h2 x
  obtain ⟨m, z, h1⟩ := h1 y
  refine ⟨n + m, z, ?_⟩
  rw [IsScalarTower.algebraMap_apply F E K, h1, map_pow, h2, ← pow_mul, ← pow_add]

namespace IntermediateField

variable (M : IntermediateField F K)

/-
**IntermediateField.isPurelyInseparable_tower_bot** 是 Mathlib 中的一个实例，位于命名空间 `Int
ermediateField`。
形式化陈述：isPurelyInseparable_tower_bot [IsPurelyInseparable F K] : IsPurelyInsepara
ble F M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.tower_bot`：IsPurelyInseparable.tower_bot [Algebra E 
K] [IsScalarTower F E K] [IsPurelyInseparable F K] : IsPurelyInseparable F E
-/
instance isPurelyInseparable_tower_bot [IsPurelyInseparable F K] : IsPurelyInseparable F M :=
  IsPurelyInseparable.tower_bot F M K
/-
**IntermediateField.isPurelyInseparable_tower_top** 是 Mathlib 中的一个实例，位于命名空间 `Int
ermediateField`。
形式化陈述：isPurelyInseparable_tower_top [IsPurelyInseparable F K] : IsPurelyInsepara
ble M K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.tower_top`：IsPurelyInseparable.tower_top [Algebra E 
K] [IsScalarTower F E K] [h : IsPurelyInseparable F K] : IsPurelyInseparable E K
-/
instance isPurelyInseparable_tower_top [IsPurelyInseparable F K] : IsPurelyInseparable M K :=
  IsPurelyInseparable.tower_top F M K

end IntermediateField

variable {E}

/-- A field extension `E / F` is purely inseparable if and only if for every element `x` of `E`,
its minimal polynomial has separable degree one. -/
/-
**isPurelyInseparable_iff_natSepDegree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPurelyInseparable_iff_natSepDegree_eq_one : IsPurelyInseparable F E ↔ fo
rall x : E, (minpoly F x).natSepDegree = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpChar.exists`：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar
 R q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPurelyInseparable_iff_pow_mem`：isPurelyInseparable_iff_pow_mem : IsPur
elyInseparable F E ↔ forall x : E, exists n : Nat, x ^ q ^ n in (algebraMap F E)
.range
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `minpoly.natSepDegree_eq_one_iff_pow_mem`：natSepDegree_eq_one_iff_pow_mem
 : (minpoly F x).natSepDegree = 1 ↔ exists n : Nat, x ^ q ^ n in (algebraMap F E
).range
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A field extension `E / F` is purely inseparable if and only if for every element
 `x` of `E`,
its minimal polynomial has separable degree one.
-/
theorem isPurelyInseparable_iff_natSepDegree_eq_one :
    IsPurelyInseparable F E ↔ ∀ x : E, (minpoly F x).natSepDegree = 1 := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  simp_rw [isPurelyInseparable_iff_pow_mem F q, minpoly.natSepDegree_eq_one_iff_pow_mem q]
/-
**IsPurelyInseparable.natSepDegree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.natSepDegree_eq_one [IsPurelyInseparable F E] (x : E) 
: (minpoly F x).natSepDegree = 1
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPurelyInseparable_iff_natSepDegree_eq_one`：isPurelyInseparable_iff_nat
SepDegree_eq_one : IsPurelyInseparable F E ↔ forall x : E, (minpoly F x).natSepD
egree = 1
-/
theorem IsPurelyInseparable.natSepDegree_eq_one [IsPurelyInseparable F E] (x : E) :
    (minpoly F x).natSepDegree = 1 :=
  (isPurelyInseparable_iff_natSepDegree_eq_one F).1 ‹_› x

/-- A field extension `E / F` of exponential characteristic `q` is purely inseparable
if and only if for every element `x` of `E`, the minimal polynomial of `x` over `F` is of form
`X ^ (q ^ n) - y` for some natural number `n` and some element `y` of `F`. -/
/-
**isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C (q : Nat) [hF : ExpChar F q
] : IsPurelyInseparable F E ↔ forall x : E, exists (n : Nat) (y : F), minpoly F 
x = X ^ q ^ n - C y
参数：q : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C`：natSepDegree_eq_one_iff_
eq_X_pow_sub_C : (minpoly F x).natSepDegree = 1 ↔ exists (n : Nat) (y : F), minp
oly F x = X ^ q ^ n - C y
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A field extension `E / F` of exponential characteristic `q` is purely inseparabl
e
if and only if for every element `x` of `E`, the minimal polynomial of `x` over 
`F` is of form
`X ^ (q ^ n) - y` for some natural number `n` and some element `y` of `F`.
-/
theorem isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C (q : ℕ) [hF : ExpChar F q] :
    IsPurelyInseparable F E ↔ ∀ x : E, ∃ (n : ℕ) (y : F), minpoly F x = X ^ q ^ n - C y := by
  simp_rw [isPurelyInseparable_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q]
/-
**IsPurelyInseparable.minpoly_eq_X_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.minpoly_eq_X_pow_sub_C (q : Nat) [ExpChar F q] [IsPure
lyInseparable F E] (x : E) : exists (n : Nat) (y : F), minpoly F x = X ^ q ^ n -
 C y
参数：q : Nat；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C`：isPurelyInseparable_iff_
minpoly_eq_X_pow_sub_C (q : Nat) [hF : ExpChar F q] : IsPurelyInseparable F E ↔ 
forall x : E, exists (n : Nat) (y : …
-/
theorem IsPurelyInseparable.minpoly_eq_X_pow_sub_C (q : ℕ) [ExpChar F q] [IsPurelyInseparable F E]
    (x : E) : ∃ (n : ℕ) (y : F), minpoly F x = X ^ q ^ n - C y :=
  (isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C F q).1 ‹_› x

/-- A field extension `E / F` of exponential characteristic `q` is purely inseparable
if and only if for every element `x` of `E`, the minimal polynomial of `x` over `F` is of form
`(X - x) ^ (q ^ n)` for some natural number `n`. -/
/-
**isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow (q : Nat) [hF : ExpChar F q
] : IsPurelyInseparable F E ↔ forall x : E, exists n : Nat, (minpoly F x).map (a
lgebraMap F E) = (X - C x) ^ q ^ n
参数：q : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `minpoly.natSepDegree_eq_one_iff_eq_X_sub_C_pow`：natSepDegree_eq_one_iff_
eq_X_sub_C_pow : (minpoly F x).natSepDegree = 1 ↔ exists n : Nat, (minpoly F x).
map (algebraMap F E) = (X - C x) ^ q…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A field extension `E / F` of exponential characteristic `q` is purely inseparabl
e
if and only if for every element `x` of `E`, the minimal polynomial of `x` over 
`F` is of form
`(X - x) ^ (q ^ n)` for some natural number `n`.
-/
theorem isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow (q : ℕ) [hF : ExpChar F q] :
    IsPurelyInseparable F E ↔
    ∀ x : E, ∃ n : ℕ, (minpoly F x).map (algebraMap F E) = (X - C x) ^ q ^ n := by
  simp_rw [isPurelyInseparable_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_eq_X_sub_C_pow q]
/-
**IsPurelyInseparable.minpoly_eq_X_sub_C_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.minpoly_eq_X_sub_C_pow (q : Nat) [ExpChar F q] [IsPure
lyInseparable F E] (x : E) : exists n : Nat, (minpoly F x).map (algebraMap F E) 
= (X - C x) ^ q ^ n
参数：q : Nat；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow`：isPurelyInseparable_iff_
minpoly_eq_X_sub_C_pow (q : Nat) [hF : ExpChar F q] : IsPurelyInseparable F E ↔ 
forall x : E, exists n : Nat, (minpo…
-/
theorem IsPurelyInseparable.minpoly_eq_X_sub_C_pow (q : ℕ) [ExpChar F q] [IsPurelyInseparable F E]
    (x : E) : ∃ n : ℕ, (minpoly F x).map (algebraMap F E) = (X - C x) ^ q ^ n :=
  (isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow F q).1 ‹_› x

variable (E) in
/-
**IsPurelyInseparable.finrank_eq_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.finrank_eq_pow (q : Nat) [ExpChar F q] [IsPurelyInsepa
rable F E] [FiniteDimensional F E] : exists n, finrank F E = q ^ n
参数：q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.finrank_bot`：∀ {F : Type u_1} [inst : Field F] {E : Ty
pe u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.finrank F ↥⊥ = 1
· 使用定理 `IntermediateField.finrank_top'`：∀ {F : Type u_1} [inst : Field F] {E : T
ype u_2} [inst_1 : Field E] [inst_2 : Algebra F E],   Module.finrank F ↥⊤ = Modu
le.finrank F E
· 使用定理 `SetLike.exists_of_lt`：exists_of_lt : p < q -> exists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `IsPurelyInseparable.minpoly_eq_X_pow_sub_C`：IsPurelyInseparable.minpoly_
eq_X_pow_sub_C (q : Nat) [ExpChar F q] [IsPurelyInseparable F E] (x : E) : exist
s (n : Nat) (y : F), minpoly F x…
· 使用定理 `IntermediateField.adjoin.finrank`：∀ {K : Type u} [inst : Field K] {L : T
ype u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegral K x → M
odule.finrank K ↥K⟮x⟯ …
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `IsPurelyInseparable.isIntegral`：∀ {F : Type u_1} {E : Type u_2} {inst : 
CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInseparab
le F E], Algebra.IsI…
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X_pow`：natDegree_X_pow : natDegree ((X : R[X]) ^ n)
 = n
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Nat.lt_mul_iff_one_lt_left`：∀ {b a : ℕ}, 0 < b → (b < a * b ↔ 1 < a)
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 39 条，此处仅展示前 30 条）
-/
lemma IsPurelyInseparable.finrank_eq_pow
    (q : ℕ) [ExpChar F q] [IsPurelyInseparable F E] [FiniteDimensional F E] :
    ∃ n, finrank F E = q ^ n := by
  suffices ∀ (F E : Type v) [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]
      [IsPurelyInseparable F E] [FiniteDimensional F E], ∃ n, finrank F E = q ^ n by
    simpa using this (⊥ : IntermediateField F E) E q
  intro F E _ _ _ q _ _ _
  generalize hd : finrank F E = d
  induction d using Nat.strongRecOn generalizing F with
  | ind d IH =>
    by_cases h : (⊥ : IntermediateField F E) = ⊤
    · rw [← finrank_top', ← h, IntermediateField.finrank_bot] at hd
      exact ⟨0, ((pow_zero q).trans hd).symm⟩
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_of_le_of_ne bot_le h :)
    obtain ⟨m, y, e⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F q x
    have : finrank F F⟮x⟯ = q ^ m := by
      rw [adjoin.finrank (Algebra.IsIntegral.isIntegral x), e, natDegree_sub_C, natDegree_X_pow]
    obtain ⟨n, hn⟩ := IH _ (by
      rw [← hd, ← finrank_mul_finrank F F⟮x⟯, Nat.lt_mul_iff_one_lt_left finrank_pos, this]
      by_contra! H
      refine hx (finrank_adjoin_simple_eq_one_iff.mp (le_antisymm (this ▸ H) ?_))
      exact Nat.one_le_iff_ne_zero.mpr Module.finrank_pos.ne') (F⟮x⟯) rfl
    exact ⟨m + n, by rw [← hd, ← finrank_mul_finrank F F⟮x⟯, hn, pow_add, this]⟩

variable (E)

variable {F E} in
/-- If an extension has finite separable degree one, then it is purely inseparable. -/
/-
**isPurelyInseparable_of_finSepDegree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPurelyInseparable_of_finSepDegree_eq_one (hdeg : finSepDegree F E = 1) :
 IsPurelyInseparable F E
参数：hdeg : finSepDegree F E = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPurelyInseparable_iff`：isPurelyInseparable_iff : IsPurelyInseparable F
 E ↔ forall x : E, IsIntegral F x ∧ (IsSeparable F x -> x in (algebraMap F E).ra
nge)
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `Field.finSepDegree_mul_finSepDegree_of_isAlgebraic`：finSepDegree_mul_fin
SepDegree_of_isAlgebraic [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebrai
c E K] : finSepDegree F E * finSepDegree…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IntermediateField.finrank_eq_one_iff`：finrank_eq_one_iff : finrank F K =
 1 ↔ K = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.finSepDegree_adjoin_simple_eq_finrank_iff`：finSepDegre
e_adjoin_simple_eq_finrank_iff (α : E) (halg : IsAlgebraic F α) : finSepDegree F
 F⟮α⟯ = finrank F F⟮α⟯ ↔ IsSeparable F α
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `mul_eq_one`：mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Field.finSepDegree_eq_zero_of_transcendental`：finSepDegree_eq_zero_of_tr
anscendental [Algebra.Transcendental F E] : finSepDegree F E = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.transcendental_iff_not_isAlgebraic`：Algebra.transcendental_iff_n
ot_isAlgebraic : Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
If an extension has finite separable degree one, then it is purely inseparable.
-/
theorem isPurelyInseparable_of_finSepDegree_eq_one
    (hdeg : finSepDegree F E = 1) : IsPurelyInseparable F E := by
  by_cases H : Algebra.IsAlgebraic F E
  · rw [isPurelyInseparable_iff]
    refine fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, fun hsep ↦ ?_⟩
    have := finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E
    rw [hdeg, mul_eq_one, (finSepDegree_adjoin_simple_eq_finrank_iff F E x
        (Algebra.IsAlgebraic.isAlgebraic x)).2 hsep,
      IntermediateField.finrank_eq_one_iff] at this
    simpa only [this.1] using! mem_adjoin_simple_self F x
  · rw [← Algebra.transcendental_iff_not_isAlgebraic] at H
    simp [finSepDegree_eq_zero_of_transcendental F E] at hdeg

namespace IsPurelyInseparable

variable [IsPurelyInseparable F E] (R L : Type*) [CommSemiring R] [Algebra R F] [Algebra R E]

/-- If `E / F` is purely inseparable, then for any reduced ring `L`, the map `(E →+* L) → (F →+* L)`
induced by `algebraMap F E` is injective. In particular, a purely inseparable field extension
is an epimorphism in the category of fields. -/
/-
**IsPurelyInseparable.injective_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsPur
elyInseparable`。
形式化陈述：injective_comp_algebraMap [CommRing L] [IsReduced L] : Function.Injective 
fun f : E ->+* L => f.comp (algebraMap F E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `IsPurelyInseparable.pow_mem`：IsPurelyInseparable.pow_mem [IsPurelyInsepa
rable F E] : exists n : Nat, x ^ q ^ n in (algebraMap F E).range
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `expChar_of_injective_ringHom`：expChar_of_injective_ringHom [NonAssocSemi
ring R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) (q : Nat)
 [hR : ExpChar R q…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `iterateFrobenius_inj`：iterateFrobenius_inj : Function.Injective (iterate
Frobenius R p n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
If `E / F` is purely inseparable, then for any reduced ring `L`, the map `(E →+*
 L) → (F →+* L)`
induced by `algebraMap F E` is injective. In particular, a purely inseparable fi
eld extension
is an epimorphism in the category of fields.
-/
theorem injective_comp_algebraMap [CommRing L] [IsReduced L] :
    Function.Injective fun f : E →+* L ↦ f.comp (algebraMap F E) := fun f g heq ↦ by
  ext x
  let q := ringExpChar F
  obtain ⟨n, y, h⟩ := IsPurelyInseparable.pow_mem F q x
  replace heq := congr($heq y)
  simp_rw [RingHom.comp_apply, h, map_pow] at heq
  nontriviality L
  have := expChar_of_injective_ringHom (f.comp (algebraMap F E)).injective q
  exact iterateFrobenius_inj L q n heq
/-
**IsPurelyInseparable.injective_restrictDomain** 是 Mathlib 中的一个定理，位于命名空间 `IsPure
lyInseparable`。
形式化陈述：injective_restrictDomain [CommRing L] [IsReduced L] [Algebra R L] [IsScala
rTower R F E] : Function.Injective (AlgHom.domRestrict (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `IsPurelyInseparable.injective_comp_algebraMap`：injective_comp_algebraMap
 [CommRing L] [IsReduced L] : Function.Injective fun f : E ->+* L => f.comp (alg
ebraMap F E)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem injective_restrictDomain [CommRing L] [IsReduced L] [Algebra R L] [IsScalarTower R F E] :
    Function.Injective (AlgHom.domRestrict (A := R) F (C := E) (D := L)) := fun _ _ eq ↦
  AlgHom.coe_ringHom_injective <| injective_comp_algebraMap F E L <| congr_arg AlgHom.toRingHom eq
/-
**IsPurelyInseparable.** 是 Mathlib 中的一个实例，位于命名空间 `IsPurelyInseparable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Field L] [PerfectField L] [Algebra F L] : Nonempty (E →ₐ[F] L) :=
  nonempty_algHom_of_splits fun x ↦ ⟨IsPurelyInseparable.isIntegral' _ _,
    have ⟨q, _⟩ := ExpChar.exists F
    PerfectField.splits_of_natSepDegree_eq_one (algebraMap F L)
      ((minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).mpr <|
        IsPurelyInseparable.minpoly_eq_X_pow_sub_C F q x)⟩
/-
**IsPurelyInseparable.bijective_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsPur
elyInseparable`。
形式化陈述：bijective_comp_algebraMap [Field L] [PerfectField L] : Function.Bijective 
fun f : E ->+* L => f.comp (algebraMap F E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.injective_comp_algebraMap`：injective_comp_algebraMap
 [CommRing L] [IsReduced L] : Function.Injective fun f : E ->+* L => f.comp (alg
ebraMap F E)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsPurelyInseparable.instNonemptyAlgHomOfPerfectField`：∀ (F : Type u) (E 
: Type v) [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] [IsPurelyIn
separable F E]   (L : Type u_2) [inst_4 : …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
-/
theorem bijective_comp_algebraMap [Field L] [PerfectField L] :
    Function.Bijective fun f : E →+* L ↦ f.comp (algebraMap F E) :=
  ⟨injective_comp_algebraMap F E L, fun g ↦ let _ := g.toAlgebra
    ⟨_, (Classical.arbitrary <| E →ₐ[F] L).comp_algebraMap⟩⟩
/-
**IsPurelyInseparable.bijective_restrictDomain** 是 Mathlib 中的一个定理，位于命名空间 `IsPure
lyInseparable`。
形式化陈述：bijective_restrictDomain [Field L] [PerfectField L] [Algebra R L] [IsScala
rTower R F E] : Function.Bijective (AlgHom.domRestrict (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.injective_restrictDomain`：injective_restrictDomain [
CommRing L] [IsReduced L] [Algebra R L] [IsScalarTower R F E] : Function.Injecti
ve (AlgHom.domRestrict (A
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsPurelyInseparable.instNonemptyAlgHomOfPerfectField`：∀ (F : Type u) (E 
: Type v) [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] [IsPurelyIn
separable F E]   (L : Type u_2) [inst_4 : …
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
-/
theorem bijective_restrictDomain [Field L] [PerfectField L] [Algebra R L] [IsScalarTower R F E] :
    Function.Bijective (AlgHom.domRestrict (A := R) F (C := E) (D := L)) :=
  ⟨injective_restrictDomain F E R L, fun g ↦ let _ := g.toAlgebra
    let f := Classical.arbitrary (E →ₐ[F] L)
    ⟨f.restrictScalars R, AlgHom.coe_ringHom_injective f.comp_algebraMap⟩⟩

end IsPurelyInseparable

/-- If `E / F` is purely inseparable, then for any reduced `F`-algebra `L`, there exists at most one
`F`-algebra homomorphism from `E` to `L`. -/
/-
**instSubsingletonAlgHomOfIsPurelyInseparable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instSubsingletonAlgHomOfIsPurelyInseparable [IsPurelyInseparable F E] (L :
 Type w) [CommRing L] [IsReduced L] [Algebra F L] : Subsingleton (E ->ₐ[F] L) wh
ere allEq f g
参数：L : Type w。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `IsPurelyInseparable.injective_comp_algebraMap`：injective_comp_algebraMap
 [CommRing L] [IsReduced L] : Function.Injective fun f : E ->+* L => f.comp (alg
ebraMap F E)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `E / F` is purely inseparable, then for any reduced `F`-algebra `L`, there ex
ists at most one
`F`-algebra homomorphism from `E` to `L`.
-/
instance instSubsingletonAlgHomOfIsPurelyInseparable [IsPurelyInseparable F E] (L : Type w)
    [CommRing L] [IsReduced L] [Algebra F L] : Subsingleton (E →ₐ[F] L) where
  allEq f g := AlgHom.coe_ringHom_injective <|
    IsPurelyInseparable.injective_comp_algebraMap F E L (by simp_rw [AlgHom.comp_algebraMap])
/-
**instUniqueAlgHomOfIsPurelyInseparable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instUniqueAlgHomOfIsPurelyInseparable [IsPurelyInseparable F E] (L : Type 
w) [CommRing L] [IsReduced L] [Algebra F L] [Algebra E L] [IsScalarTower F E L] 
: Unique (E ->ₐ[F] L)
参数：L : Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniqueAlgHomOfIsPurelyInseparable [IsPurelyInseparable F E] (L : Type w)
    [CommRing L] [IsReduced L] [Algebra F L] [Algebra E L] [IsScalarTower F E L] :
    Unique (E →ₐ[F] L) := uniqueOfSubsingleton (IsScalarTower.toAlgHom F E L)

/-- If `E / F` is purely inseparable, then `Field.Emb F E` has exactly one element. -/
/-
**instUniqueEmbOfIsPurelyInseparable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instUniqueEmbOfIsPurelyInseparable [IsPurelyInseparable F E] : Unique (Emb
 F E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E / F` is purely inseparable, then `Field.Emb F E` has exactly one element.
-/
instance instUniqueEmbOfIsPurelyInseparable [IsPurelyInseparable F E] :
    Unique (Emb F E) := instUniqueAlgHomOfIsPurelyInseparable F E _

/-- A purely inseparable extension has finite separable degree one. -/
/-
**IsPurelyInseparable.finSepDegree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.finSepDegree_eq_one [IsPurelyInseparable F E] : finSep
Degree F E = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_unique`：card_unique [Nonempty α] [Subsingleton α] : Nat.card α 
= 1
· 使用定理 `IsPurelyInseparable.instNonemptyAlgHomOfPerfectField`：∀ (F : Type u) (E 
: Type v) [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] [IsPurelyIn
separable F E]   (L : Type u_2) [inst_4 : …
· 使用定理 `IsAlgClosed.perfectField`：∀ (k : Type u) [inst : Field k] [IsAlgClosed k
], PerfectField k
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R

--- 原说明 ---
A purely inseparable extension has finite separable degree one.
-/
theorem IsPurelyInseparable.finSepDegree_eq_one [IsPurelyInseparable F E] :
    finSepDegree F E = 1 := Nat.card_unique

/-- A purely inseparable extension has separable degree one. -/
/-
**IsPurelyInseparable.sepDegree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.sepDegree_eq_one [IsPurelyInseparable F E] : sepDegree
 F E = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.sepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] [inst
_1 : Field E] [inst_2 : Algebra F E],   Field.sepDegree F E = Module.rank F ↥(se
parableClo…
· 使用定理 `separableClosure.eq_bot_of_isPurelyInseparable`：separableClosure.eq_bot_
of_isPurelyInseparable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F 
E] [IsPurelyInseparable F E] : separ…
· 使用定理 `IntermediateField.rank_bot`：∀ {F : Type u_1} [inst : Field F] {E : Type 
u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.rank F ↥⊥ = 1

--- 原说明 ---
A purely inseparable extension has separable degree one.
-/
theorem IsPurelyInseparable.sepDegree_eq_one [IsPurelyInseparable F E] :
    sepDegree F E = 1 := by
  rw [sepDegree, separableClosure.eq_bot_of_isPurelyInseparable, IntermediateField.rank_bot]

/-- A purely inseparable extension has inseparable degree equal to degree. -/
/-
**IsPurelyInseparable.insepDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.insepDegree_eq [IsPurelyInseparable F E] : insepDegree
 F E = Module.rank F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.insepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] [in
st_1 : Field E] [inst_2 : Algebra F E],   Field.insepDegree F E = Module.rank (↥
(separableCl…
· 使用定理 `separableClosure.eq_bot_of_isPurelyInseparable`：separableClosure.eq_bot_
of_isPurelyInseparable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F 
E] [IsPurelyInseparable F E] : separ…
· 使用定理 `IntermediateField.rank_bot'`：∀ {F : Type u_1} [inst : Field F] {E : Type
 u_2} [inst_1 : Field E] [inst_2 : Algebra F E],   Module.rank (↥⊥) E = Module.r
ank F E

--- 原说明 ---
A purely inseparable extension has inseparable degree equal to degree.
-/
theorem IsPurelyInseparable.insepDegree_eq [IsPurelyInseparable F E] :
    insepDegree F E = Module.rank F E := by
  rw [insepDegree, separableClosure.eq_bot_of_isPurelyInseparable, rank_bot']

/-- A purely inseparable extension has finite inseparable degree equal to degree. -/
/-
**IsPurelyInseparable.finInsepDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.finInsepDegree_eq [IsPurelyInseparable F E] : finInsep
Degree F E = finrank F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPurelyInseparable.insepDegree_eq`：IsPurelyInseparable.insepDegree_eq [
IsPurelyInseparable F E] : insepDegree F E = Module.rank F E

--- 原说明 ---
A purely inseparable extension has finite inseparable degree equal to degree.
-/
theorem IsPurelyInseparable.finInsepDegree_eq [IsPurelyInseparable F E] :
    finInsepDegree F E = finrank F E := congr(Cardinal.toNat $(insepDegree_eq F E))

/-- An extension is purely inseparable if and only if it has finite separable degree one. -/
/-
**isPurelyInseparable_iff_finSepDegree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPurelyInseparable_iff_finSepDegree_eq_one : IsPurelyInseparable F E ↔ fi
nSepDegree F E = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.finSepDegree_eq_one`：IsPurelyInseparable.finSepDegre
e_eq_one [IsPurelyInseparable F E] : finSepDegree F E = 1
· 使用定理 `isPurelyInseparable_of_finSepDegree_eq_one`：isPurelyInseparable_of_finSe
pDegree_eq_one (hdeg : finSepDegree F E = 1) : IsPurelyInseparable F E

--- 原说明 ---
An extension is purely inseparable if and only if it has finite separable degree
 one.
-/
theorem isPurelyInseparable_iff_finSepDegree_eq_one :
    IsPurelyInseparable F E ↔ finSepDegree F E = 1 :=
  ⟨fun _ ↦ IsPurelyInseparable.finSepDegree_eq_one F E,
    fun h ↦ isPurelyInseparable_of_finSepDegree_eq_one h⟩

/-- An extension `E / F` is purely inseparable if and only there is at most one
  embedding `E →ₐ[F] AlgebraicClosure E` -/
/-
**isPurelyInseparable_iff_subsingleton_emb** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPurelyInseparable_iff_subsingleton_emb : IsPurelyInseparable F E ↔ Subsi
ngleton (Field.Emb F E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPurelyInseparable_iff_finSepDegree_eq_one`：isPurelyInseparable_iff_fin
SepDegree_eq_one : IsPurelyInseparable F E ↔ finSepDegree F E = 1
· 使用定理 `Field.finSepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] [i
nst_1 : Field E] [inst_2 : Algebra F E],   Field.finSepDegree F E = Nat.card (Fi
eld.Emb F E)
· 使用定理 `Nat.card_eq_one_iff_unique`：card_eq_one_iff_unique : Nat.card α = 1 ↔ Su
bsingleton α ∧ Nonempty α
· 使用定理 `and_iff_left_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ a) ↔ a → b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
An extension `E / F` is purely inseparable if and only there is at most one
  embedding `E →ₐ[F] AlgebraicClosure E`
-/
theorem isPurelyInseparable_iff_subsingleton_emb :
    IsPurelyInseparable F E ↔ Subsingleton (Field.Emb F E) := by
  rw [isPurelyInseparable_iff_finSepDegree_eq_one, Field.finSepDegree, Nat.card_eq_one_iff_unique,
    and_iff_left_iff_imp]
  infer_instance
/-
**isSeparable_iff_finInsepDegree_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSeparable_iff_finInsepDegree_eq_one : Algebra.IsSeparable F K ↔ finInsep
Degree F K = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `separableClosure.eq_top_iff`：separableClosure.eq_top_iff : separableClos
ure F E = ⊤ ↔ Algebra.IsSeparable F E
· 使用引理 `IntermediateField.finrank_eq_one_iff_eq_top`：finrank_eq_one_iff_eq_top {
K : IntermediateField F E} : Module.finrank K E = 1 ↔ K = ⊤
· 使用定理 `Field.finInsepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] 
[inst_1 : Field E] [inst_2 : Algebra F E],   Field.finInsepDegree F E = Module.f
inrank (↥(separ…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isSeparable_iff_finInsepDegree_eq_one :
    Algebra.IsSeparable F K ↔ finInsepDegree F K = 1 := by
  rw [← separableClosure.eq_top_iff, ← IntermediateField.finrank_eq_one_iff_eq_top, finInsepDegree]

variable {F E} in
/-- An algebraic extension is purely inseparable if and only if all of its finite-dimensional
subextensions are purely inseparable. -/
/-
**isPurelyInseparable_iff_fd_isPurelyInseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPurelyInseparable_iff_fd_isPurelyInseparable [Algebra.IsAlgebraic F E] :
 IsPurelyInseparable F E ↔ forall L : IntermediateField F E, FiniteDimensional F
 L -> IsPurelyInseparable F L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.tower_bot`：IsPurelyInseparable.tower_bot [Algebra E 
K] [IsScalarTower F E K] [IsPurelyInseparable F K] : IsPurelyInseparable F E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isPurelyInseparable_iff`：isPurelyInseparable_iff : IsPurelyInseparable F
 E ↔ forall x : E, IsIntegral F x ∧ (IsSeparable F x -> x in (algebraMap F E).ra
nge)
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `IsPurelyInseparable.inseparable'`：∀ {F : Type u_1} {E : Type u_2} {inst 
: CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInsepar
able F E] (x : E), IsS…
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.minpoly_eq`：minpoly_eq (x : S) : minpoly K x = minpoly
 K (x : L)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
An algebraic extension is purely inseparable if and only if all of its finite-di
mensional
subextensions are purely inseparable.
-/
theorem isPurelyInseparable_iff_fd_isPurelyInseparable [Algebra.IsAlgebraic F E] :
    IsPurelyInseparable F E ↔
    ∀ L : IntermediateField F E, FiniteDimensional F L → IsPurelyInseparable F L := by
  refine ⟨fun _ _ _ ↦ IsPurelyInseparable.tower_bot F _ E,
    fun h ↦ isPurelyInseparable_iff.2 fun x ↦ ?_⟩
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  refine ⟨hx, fun _ ↦ ?_⟩
  obtain ⟨y, h⟩ := (h _ (adjoin.finiteDimensional hx)).inseparable' _ <|
    show Separable (minpoly F (AdjoinSimple.gen F x)) by rwa [minpoly_eq]
  exact ⟨y, congr_arg (algebraMap _ E) h⟩

/-- A purely inseparable extension is normal. -/
/-
**IsPurelyInseparable.normal** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.normal [IsPurelyInseparable F E] : Normal F E where to
IsAlgebraic
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.isAlgebraic`：IsPurelyInseparable.isAlgebraic [Nontri
vial F] [IsPurelyInseparable F E] : Algebra.IsAlgebraic F E
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsPurelyInseparable.minpoly_eq_X_sub_C_pow`：IsPurelyInseparable.minpoly_
eq_X_sub_C_pow (q : Nat) [ExpChar F q] [IsPurelyInseparable F E] (x : E) : exist
s n : Nat, (minpoly F x).map (al…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.pow`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R}, f.Splits → ∀ (n : ℕ), (f ^ n).Splits
· 使用定理 `Polynomial.Splits.X_sub_C`：∀ {R : Type u_1} [inst : Ring R] (a : R), (Po
lynomial.X - Polynomial.C a).Splits

--- 原说明 ---
A purely inseparable extension is normal.
-/
instance IsPurelyInseparable.normal [IsPurelyInseparable F E] : Normal F E where
  toIsAlgebraic := isAlgebraic F E
  splits' x := by
    obtain ⟨n, h⟩ := IsPurelyInseparable.minpoly_eq_X_sub_C_pow F (ringExpChar F) x
    rw [h]
    exact Splits.pow (Splits.X_sub_C _) _

/-- If `E / F` is algebraic, then `E` is purely inseparable over the
separable closure of `F` in `E`. -/
@[stacks 030K "$E/E_{sep}$ is purely inseparable."]
/-
**separableClosure.isPurelyInseparable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：separableClosure.isPurelyInseparable [Algebra.IsAlgebraic F E] : IsPurelyI
nseparable (separableClosure F E) E
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isPurelyInseparable_iff`：isPurelyInseparable_iff : IsPurelyInseparable F
 E ↔ forall x : E, IsIntegral F x ∧ (IsSeparable F x -> x in (algebraMap F E).ra
nge)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `IsAlgebraic.tower_top`：IsAlgebraic.tower_top {x : A} (A_alg : IsAlgebrai
c K x) : IsAlgebraic L x
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`：Intermediat
eField.isSeparable_adjoin_simple_iff_isSeparable {x : E} : Algebra.IsSeparable F
 F⟮x⟯ ↔ IsSeparable F x
· 使用定理 `Algebra.IsSeparable.trans`：Algebra.IsSeparable.trans [Algebra E K] [IsSc
alarTower F E K] [Algebra.IsSeparable F E] [Algebra.IsSeparable E K] : Algebra.I
sSeparable F K
· 使用定理 `IntermediateField.instIsScalarTowerSubtypeMem_1`：∀ {K : Type u_1} {L : T
ype u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] {S : Interme
diateField K L}   {E : Type u_4} [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯
· 使用定理 `mem_separableClosure_iff`：mem_separableClosure_iff {x : E} : x in separa
bleClosure F E ↔ IsSeparable F x
· 使用引理 `IntermediateField.isSeparable_of_mem_isSeparable`：IntermediateField.isSe
parable_of_mem_isSeparable {L : IntermediateField F E} [Algebra.IsSeparable F L]
 {x : E} (h : x in L) : IsSeparable F …

--- 原说明 ---
If `E / F` is algebraic, then `E` is purely inseparable over the
separable closure of `F` in `E`.
-/
instance separableClosure.isPurelyInseparable [Algebra.IsAlgebraic F E] :
    IsPurelyInseparable (separableClosure F E) E := isPurelyInseparable_iff.2 fun x ↦ by
  set L := separableClosure F E
  refine ⟨(IsAlgebraic.tower_top L (Algebra.IsAlgebraic.isAlgebraic (R := F) x)).isIntegral,
    fun h ↦ ?_⟩
  have := (isSeparable_adjoin_simple_iff_isSeparable L E).2 h
  have : Algebra.IsSeparable F (restrictScalars F L⟮x⟯) := Algebra.IsSeparable.trans F L L⟮x⟯
  have hx : x ∈ L⟮x⟯.restrictScalars F := mem_adjoin_simple_self _ x
  exact ⟨⟨x, mem_separableClosure_iff.2 <| isSeparable_of_mem_isSeparable F E hx⟩, rfl⟩

open Cardinal in
/-
**Field.Emb.cardinal_separableClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Field.Emb.cardinal_separableClosure [Algebra.IsAlgebraic F E] : #(Field.Em
b F <| separableClosure F E) = #(Field.Emb F E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsPurelyInseparable.instNonemptyAlgHomOfPerfectField`：∀ (F : Type u) (E 
: Type v) [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] [IsPurelyIn
separable F E]   (L : Type u_2) [inst_4 : …
· 使用定理 `IsAlgClosed.perfectField`：∀ (k : Type u) [inst : Field k] [IsAlgClosed k
], PerfectField k
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem Field.Emb.cardinal_separableClosure [Algebra.IsAlgebraic F E] :
    #(Field.Emb F <| separableClosure F E) = #(Field.Emb F E) := by
  rw [← (embProdEmbOfIsAlgebraic F (separableClosure F E) E).cardinal_eq,
    mk_prod, mk_eq_one (Emb _ E), lift_one, mul_one, lift_id]
/-
**finInsepDegree_eq_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finInsepDegree_eq_pow (q : Nat) [ExpChar F q] [FiniteDimensional F E] : ex
ists n, finInsepDegree F E = q ^ n
参数：q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsPurelyInseparable.finrank_eq_pow`：IsPurelyInseparable.finrank_eq_pow (
q : Nat) [ExpChar F q] [IsPurelyInseparable F E] [FiniteDimensional F E] : exist
s n, finrank F E = q ^ n
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
lemma finInsepDegree_eq_pow (q : ℕ) [ExpChar F q] [FiniteDimensional F E] :
    ∃ n, finInsepDegree F E = q ^ n :=
  IsPurelyInseparable.finrank_eq_pow ..

/-- An intermediate field of `E / F` contains the separable closure of `F` in `E`
if `E` is purely inseparable over it. -/
/-
**separableClosure_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separableClosure_le (L : IntermediateField F E) [h : IsPurelyInseparable L
 E] : separableClosure F E <= L
参数：L : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.inseparable'`：∀ {F : Type u_1} {E : Type u_2} {inst 
: CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInsepar
able F E] (x : E), IsS…
· 使用定理 `IsSeparable.tower_top`：IsSeparable.tower_top {x : E} (h : IsSeparable F 
x) : IsSeparable L x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_separableClosure_iff`：mem_separableClosure_iff {x : E} : x in separa
bleClosure F E ↔ IsSeparable F x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
An intermediate field of `E / F` contains the separable closure of `F` in `E`
if `E` is purely inseparable over it.
-/
theorem separableClosure_le (L : IntermediateField F E)
    [h : IsPurelyInseparable L E] : separableClosure F E ≤ L := fun x hx ↦ by
  obtain ⟨y, rfl⟩ := h.inseparable' _ <|
    IsSeparable.tower_top L (mem_separableClosure_iff.1 hx)
  exact y.2

/-- If `E / F` is algebraic, then an intermediate field of `E / F` contains the
separable closure of `F` in `E` if and only if `E` is purely inseparable over it. -/
/-
**separableClosure_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separableClosure_le_iff [Algebra.IsAlgebraic F E] (L : IntermediateField F
 E) : separableClosure F E <= L ↔ IsPurelyInseparable L E
参数：L : IntermediateField F E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `IsPurelyInseparable.tower_top`：IsPurelyInseparable.tower_top [Algebra E 
K] [IsScalarTower F E K] [h : IsPurelyInseparable F K] : IsPurelyInseparable E K
· 使用定理 `separableClosure_le`：separableClosure_le (L : IntermediateField F E) [h 
: IsPurelyInseparable L E] : separableClosure F E <= L

--- 原说明 ---
If `E / F` is algebraic, then an intermediate field of `E / F` contains the
separable closure of `F` in `E` if and only if `E` is purely inseparable over it
.
-/
theorem separableClosure_le_iff [Algebra.IsAlgebraic F E] (L : IntermediateField F E) :
    separableClosure F E ≤ L ↔ IsPurelyInseparable L E := by
  refine ⟨fun h ↦ ?_, fun _ ↦ separableClosure_le F E L⟩
  let := (inclusion h).toAlgebra
  let : SMul (separableClosure F E) L := Algebra.toSMul
  have : IsScalarTower (separableClosure F E) L E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact IsPurelyInseparable.tower_top (separableClosure F E) L E

/-- If an intermediate field of `E / F` is separable over `F`, and `E` is purely inseparable
over it, then it is equal to the separable closure of `F` in `E`. -/
/-
**eq_separableClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_separableClosure (L : IntermediateField F E) [Algebra.IsSeparable F L] 
[IsPurelyInseparable L E] : L = separableClosure F E
参数：L : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_separableClosure`：le_separableClosure (L : IntermediateField F E) [Al
gebra.IsSeparable F L] : L <= separableClosure F E
· 使用定理 `separableClosure_le`：separableClosure_le (L : IntermediateField F E) [h 
: IsPurelyInseparable L E] : separableClosure F E <= L

--- 原说明 ---
If an intermediate field of `E / F` is separable over `F`, and `E` is purely ins
eparable
over it, then it is equal to the separable closure of `F` in `E`.
-/
theorem eq_separableClosure (L : IntermediateField F E)
    [Algebra.IsSeparable F L] [IsPurelyInseparable L E] : L = separableClosure F E :=
  le_antisymm (le_separableClosure F E L) (separableClosure_le F E L)

open separableClosure in
/-- If `E / F` is algebraic, then an intermediate field of `E / F` is equal to the separable closure
of `F` in `E` if and only if it is separable over `F`, and `E` is purely inseparable
over it. -/
/-
**eq_separableClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_separableClosure_iff [Algebra.IsAlgebraic F E] (L : IntermediateField F
 E) : L = separableClosure F E ↔ Algebra.IsSeparable F L ∧ IsPurelyInseparable L
 E
参数：L : IntermediateField F E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_separableClosure`：eq_separableClosure (L : IntermediateField F E) [Al
gebra.IsSeparable F L] [IsPurelyInseparable L E] : L = separableClosure F E

--- 原说明 ---
If `E / F` is algebraic, then an intermediate field of `E / F` is equal to the s
eparable closure
of `F` in `E` if and only if it is separable over `F`, and `E` is purely insepar
able
over it.
-/
theorem eq_separableClosure_iff [Algebra.IsAlgebraic F E] (L : IntermediateField F E) :
    L = separableClosure F E ↔ Algebra.IsSeparable F L ∧ IsPurelyInseparable L E :=
  ⟨by rintro rfl; exact ⟨isSeparable F E, isPurelyInseparable F E⟩,
   fun ⟨_, _⟩ ↦ eq_separableClosure F E L⟩

/-- If `L` is an algebraically closed field containing `E`, such that the map
`(E →+* L) → (F →+* L)` induced by `algebraMap F E` is injective, then `E / F` is
purely inseparable. As a corollary, epimorphisms in the category of fields must be
purely inseparable extensions. -/
/-
**IsPurelyInseparable.of_injective_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.of_injective_comp_algebraMap (L : Type w) [Field L] [I
sAlgClosed L] [Nonempty (E ->+* L)] (h : Function.Injective fun f : E ->+* L => 
f.comp (algebraMap F E)) : IsPurelyInseparable F E
参数：L : Type w；E ->+* L；h : Function.Injective fun f : E ->+* L => f.comp (algebr
aMap F E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPurelyInseparable_iff_finSepDegree_eq_one`：isPurelyInseparable_iff_fin
SepDegree_eq_one : IsPurelyInseparable F E ↔ finSepDegree F E = 1
· 使用定理 `Field.finSepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] [i
nst_1 : Field E] [inst_2 : Algebra F E],   Field.finSepDegree F E = Nat.card (Fi
eld.Emb F E)
· 使用定理 `Nat.card_eq_one_iff_unique`：card_eq_one_iff_unique : Nat.card α = 1 ↔ Su
bsingleton α ∧ Nonempty α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
· 使用定理 `Function.Injective.comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort 
u_3} {g : β → γ}, Function.Injective g → Function.Injective fun x => g ∘ x
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
If `L` is an algebraically closed field containing `E`, such that the map
`(E →+* L) → (F →+* L)` induced by `algebraMap F E` is injective, then `E / F` i
s
purely inseparable. As a corollary, epimorphisms in the category of fields must 
be
purely inseparable extensions.
-/
theorem IsPurelyInseparable.of_injective_comp_algebraMap (L : Type w) [Field L] [IsAlgClosed L]
    [Nonempty (E →+* L)] (h : Function.Injective fun f : E →+* L ↦ f.comp (algebraMap F E)) :
    IsPurelyInseparable F E := by
  rw [isPurelyInseparable_iff_finSepDegree_eq_one, finSepDegree, Nat.card_eq_one_iff_unique]
  let := (Classical.arbitrary (E →+* L)).toAlgebra
  let j : AlgebraicClosure E →ₐ[E] L := IsAlgClosed.lift
  exact ⟨⟨fun f g ↦ DFunLike.ext' <| j.injective.comp_left (congr_arg (⇑) <|
    @h (j.toRingHom.comp f) (j.toRingHom.comp g) (by ext; simp))⟩, inferInstance⟩

end Field

namespace IntermediateField

/-
**IntermediateField.isPurelyInseparable_bot** 是 Mathlib 中的一个实例，位于命名空间 `Intermedi
ateField`。
形式化陈述：isPurelyInseparable_bot : IsPurelyInseparable F (⊥ : IntermediateField F E
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.isPurelyInseparable`：AlgEquiv.isPurelyInseparable (e : K ≃ₐ[F] 
E) [IsPurelyInseparable F K] : IsPurelyInseparable F E
-/
instance isPurelyInseparable_bot : IsPurelyInseparable F (⊥ : IntermediateField F E) :=
  (botEquiv F E).symm.isPurelyInseparable

end IntermediateField

/-- If `E` is an algebraic closure of `F`, then `F` is separably closed if and only if `E / F` is
purely inseparable. -/
/-
**isSepClosed_iff_isPurelyInseparable_algebraicClosure** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：isSepClosed_iff_isPurelyInseparable_algebraicClosure [IsAlgClosure F E] : 
IsSepClosed F ↔ IsPurelyInseparable F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsAlgClosure.isAlgebraic`：∀ {R : Type u} {K : Type v} {inst : CommRing R
} {inst_1 : Field K} {inst_2 : Algebra R K}   {inst_3 : Module.IsTorsionFree R K
} [self : IsAl…
· 使用定理 `IsAlgClosure.isAlgClosed`：∀ (R : Type u) {K : Type v} {inst : CommRing R
} {inst_1 : Field K} {inst_2 : Algebra R K}   {inst_3 : Module.IsTorsionFree R K
} [self : IsAl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSepClosed.separableClosure_eq_bot_iff`：IsSepClosed.separableClosure_eq
_bot_iff [IsSepClosed E] : separableClosure F E = ⊥ ↔ IsSepClosed F
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `separableClosure.eq_bot_iff`：separableClosure.eq_bot_iff {F : Type u} {E
 : Type v} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E] : separab
leClosure F E = ⊥…

--- 原说明 ---
If `E` is an algebraic closure of `F`, then `F` is separably closed if and only 
if `E / F` is
purely inseparable.
-/
theorem isSepClosed_iff_isPurelyInseparable_algebraicClosure [IsAlgClosure F E] :
    IsSepClosed F ↔ IsPurelyInseparable F E :=
  ⟨fun _ ↦ inferInstance, fun H ↦ by
    have := IsAlgClosure.isAlgClosed F (K := E)
    rwa [← separableClosure.eq_bot_iff, IsSepClosed.separableClosure_eq_bot_iff] at H⟩

variable {F E} in
/-- If `E / F` is an algebraic extension, `F` is separably closed,
then `E` is also separably closed. -/
/-
**Algebra.IsAlgebraic.isSepClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.isSepClosed [Algebra.IsAlgebraic F E] [IsSepClosed F] 
: IsSepClosed E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.trans`：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3
) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebr
a R S] [inst_4 …
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isSepClosed_iff_isPurelyInseparable_algebraicClosure`：isSepClosed_iff_is
PurelyInseparable_algebraicClosure [IsAlgClosure F E] : IsSepClosed F ↔ IsPurely
Inseparable F E
· 使用定理 `AlgebraicClosure.instIsAlgClosureOfIsAlgebraic`：∀ (k : Type u) [inst : F
ield k] {L : Type u_1} [inst_1 : Field L] [inst_2 : Algebra k L] [Algebra.IsAlge
braic k L],   IsAlgClosure k (Algebr…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsPurelyInseparable.tower_top`：IsPurelyInseparable.tower_top [Algebra E 
K] [IsScalarTower F E K] [h : IsPurelyInseparable F K] : IsPurelyInseparable E K

--- 原说明 ---
If `E / F` is an algebraic extension, `F` is separably closed,
then `E` is also separably closed.
-/
theorem Algebra.IsAlgebraic.isSepClosed [Algebra.IsAlgebraic F E]
    [IsSepClosed F] : IsSepClosed E :=
  have : Algebra.IsAlgebraic F (AlgebraicClosure E) := .trans F E _
  (isSepClosed_iff_isPurelyInseparable_algebraicClosure E _).mpr
    (IsPurelyInseparable.tower_top F E <| AlgebraicClosure E)

namespace Field

/-- If `E / F` is algebraic, then the `Field.finSepDegree F E` is equal to `Field.sepDegree F E`
as a natural number. This means that the cardinality of `Field.Emb F E` and the degree of
`(separableClosure F E) / F` are both finite or infinite, and when they are finite, they
coincide. -/
@[stacks 09HJ "`sepDegree` is defined as the right-hand side of 09HJ"]
/-
**Field.finSepDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：finSepDegree_eq [Algebra.IsAlgebraic F E] : finSepDegree F E = Cardinal.to
Nat (sepDegree F E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Field.finSepDegree_mul_finSepDegree_of_isAlgebraic`：finSepDegree_mul_fin
SepDegree_of_isAlgebraic [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebrai
c E K] : finSepDegree F E * finSepDegree…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsPurelyInseparable.finSepDegree_eq_one`：IsPurelyInseparable.finSepDegre
e_eq_one [IsPurelyInseparable F E] : finSepDegree F E = 1
· 使用定理 `Field.finSepDegree_eq_finrank_of_isSeparable`：finSepDegree_eq_finrank_of
_isSeparable [Algebra.IsSeparable F E] : finSepDegree F E = finrank F E

--- 原说明 ---
If `E / F` is algebraic, then the `Field.finSepDegree F E` is equal to `Field.se
pDegree F E`
as a natural number. This means that the cardinality of `Field.Emb F E` and the 
degree of
`(separableClosure F E) / F` are both finite or infinite, and when they are fini
te, they
coincide.
-/
theorem finSepDegree_eq [Algebra.IsAlgebraic F E] :
    finSepDegree F E = Cardinal.toNat (sepDegree F E) := by
  have h := finSepDegree_mul_finSepDegree_of_isAlgebraic F (separableClosure F E) E |>.symm
  rwa [finSepDegree_eq_finrank_of_isSeparable F (separableClosure F E),
    IsPurelyInseparable.finSepDegree_eq_one (separableClosure F E) E, mul_one] at h

/-- The finite separable degree multiply by the finite inseparable degree is equal
to the (finite) field extension degree. -/
/-
**Field.finSepDegree_mul_finInsepDegree** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：finSepDegree_mul_finInsepDegree : finSepDegree F E * finInsepDegree F E = 
finrank F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Field.sepDegree_mul_insepDegree`：sepDegree_mul_insepDegree : sepDegree F
 E * insepDegree F E = Module.rank F E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Field.finSepDegree_eq`：finSepDegree_eq [Algebra.IsAlgebraic F E] : finSe
pDegree F E = Cardinal.toNat (sepDegree F E)
· 使用定理 `Cardinal.toNat_mul`：toNat_mul (x y : Cardinal) : toNat (x * y) = toNat x
 * toNat y
· 使用定理 `Field.finInsepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] 
[inst_1 : Field E] [inst_2 : Algebra F E],   Field.finInsepDegree F E = Module.f
inrank (↥(separ…
· 使用定理 `Module.finrank_of_infinite_dimensional`：finrank_of_infinite_dimensional 
(h : ¬FiniteDimensional K V) : finrank K V = 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Algebra.IsAlgebraic.trans`：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3
) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebr
a R S] [inst_4 …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
The finite separable degree multiply by the finite inseparable degree is equal
to the (finite) field extension degree.
-/
theorem finSepDegree_mul_finInsepDegree : finSepDegree F E * finInsepDegree F E = finrank F E := by
  by_cases halg : Algebra.IsAlgebraic F E
  · have := congr_arg Cardinal.toNat (sepDegree_mul_insepDegree F E)
    rwa [Cardinal.toNat_mul, ← finSepDegree_eq F E] at this
  rw [finInsepDegree, finrank_of_infinite_dimensional (K := F) (V := E) fun _ ↦
      halg (Algebra.IsAlgebraic.of_finite F E),
    finrank_of_infinite_dimensional (K := separableClosure F E) (V := E) fun _ ↦
      halg (.trans _ (separableClosure F E) _),
    mul_zero]

end Field

namespace separableClosure

variable [Algebra E K] [IsScalarTower F E K] {F E}

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic and `K / E`
is separable, then `E` adjoin `separableClosure F K` is equal to `K`. It is a special case of
`separableClosure.adjoin_eq_of_isAlgebraic`, and is an intermediate result used to prove it. -/
/-
**separableClosure.adjoin_eq_of_isAlgebraic_of_isSeparable** 是 Mathlib 中的一个引理，位于
命名空间 `separableClosure`。
形式化陈述：adjoin_eq_of_isAlgebraic_of_isSeparable [Algebra.IsAlgebraic F E] [Algebra
.IsSeparable E K] : adjoin E (separableClosure F K : Set K) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.isSeparable_tower_top_of_isSeparable`：Algebra.isSeparable_tower_
top_of_isSeparable [Algebra.IsSeparable F E] : Algebra.IsSeparable L E
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Algebra.IsAlgebraic.trans`：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3
) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebr
a R S] [inst_4 …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsPurelyInseparable.tower_top`：IsPurelyInseparable.tower_top [Algebra E 
K] [IsScalarTower F E K] [h : IsPurelyInseparable F K] : IsPurelyInseparable E K
· 使用定理 `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`：IsPurelyInsepa
rable.surjective_algebraMap_of_isSeparable [IsPurelyInseparable F E] [Algebra.Is
Separable F E] : Function.Surjective (algebraM…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is algebraic and `K
 / E`
is separable, then `E` adjoin `separableClosure F K` is equal to `K`. It is a sp
ecial case of
`separableClosure.adjoin_eq_of_isAlgebraic`, and is an intermediate result used 
to prove it.
-/
lemma adjoin_eq_of_isAlgebraic_of_isSeparable [Algebra.IsAlgebraic F E]
    [Algebra.IsSeparable E K] : adjoin E (separableClosure F K : Set K) = ⊤ :=
  top_unique fun x _ ↦ by
    set S := separableClosure F K
    set L := adjoin E (S : Set K)
    have := Algebra.isSeparable_tower_top_of_isSeparable E L K
    let i : S →+* L := Subsemiring.inclusion fun x hx ↦ subset_adjoin E (S : Set K) hx
    let _ : Algebra S L := i.toAlgebra
    have : IsScalarTower S L K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
    have := Algebra.IsAlgebraic.trans F E K
    have : IsPurelyInseparable S K := separableClosure.isPurelyInseparable F K
    have := IsPurelyInseparable.tower_top S L K
    obtain ⟨y, rfl⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable L K x
    exact y.2

set_option backward.isDefEq.respectTransparency.types false in
/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then
`E` adjoin `separableClosure F K` is equal to `separableClosure E K`. -/
/-
**separableClosure.adjoin_eq_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `separable
Closure`。
形式化陈述：adjoin_eq_of_isAlgebraic [Algebra.IsAlgebraic F E] : adjoin E (separableCl
osure F K) = separableClosure E K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `separableClosure.adjoin_eq_of_isAlgebraic_of_isSeparable`：adjoin_eq_of_i
sAlgebraic_of_isSeparable [Algebra.IsAlgebraic F E] [Algebra.IsSeparable E K] : 
adjoin E (separableClosure F K : Set K) = ⊤
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.lift_adjoin`：lift_adjoin (K : IntermediateField F E) (
S : Set K) : lift (adjoin F S) = adjoin F (Subtype.val '' S)
· 使用定理 `IntermediateField.lift_top`：lift_top (K : IntermediateField F E) : lift 
(F
· 使用定理 `separableClosure.map_eq_of_separableClosure_eq_bot`：separableClosure.map
_eq_of_separableClosure_eq_bot [Algebra E K] [IsScalarTower F E K] (h : separabl
eClosure E K = ⊥) : (separableClosure F …
· 使用定理 `separableClosure.separableClosure_eq_bot`：separableClosure.separableClos
ure_eq_bot : separableClosure (separableClosure F E) E = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then
`E` adjoin `separableClosure F K` is equal to `separableClosure E K`.
-/
theorem adjoin_eq_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    adjoin E (separableClosure F K) = separableClosure E K := by
  set S := separableClosure E K
  have h := congr_arg lift (adjoin_eq_of_isAlgebraic_of_isSeparable (F := F) S)
  rw [lift_top, lift_adjoin] at h
  have : IsScalarTower F S K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← h, ← map_eq_of_separableClosure_eq_bot F (separableClosure_eq_bot E K)]
  simp only [S, coe_map, IsScalarTower.coe_toAlgHom', IntermediateField.algebraMap_apply]

end separableClosure

section

open TensorProduct

section Subalgebra

variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] (p : ℕ) [ExpChar A p]

/-- The perfect closure of `R` in `A` are the elements `x : A` such that `x ^ p ^ n`
is in `R` for some `n`, where `p` is the exponential characteristic of `R`. -/
/-
**Subalgebra.perfectClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subalgebra.perfectClosure : Subalgebra R A where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The perfect closure of `R` in `A` are the elements `x : A` such that `x ^ p ^ n`
is in `R` for some `n`, where `p` is the exponential characteristic of `R`.
-/
def Subalgebra.perfectClosure : Subalgebra R A where
  carrier := {x : A | ∃ n : ℕ, x ^ p ^ n ∈ (algebraMap R A).rangeS}
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    use n + m
    rw [add_pow_expChar_pow, pow_add, pow_mul, mul_comm (_ ^ n), pow_mul]
    exact add_mem (pow_mem hx _) (pow_mem hy _)
  mul_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    use n + m
    rw [mul_pow, pow_add, pow_mul, mul_comm (_ ^ n), pow_mul]
    exact mul_mem (pow_mem hx _) (pow_mem hy _)
  algebraMap_mem' := fun x ↦ ⟨0, by rw [pow_zero, pow_one]; exact ⟨x, rfl⟩⟩

variable {R A p}
/-
**Subalgebra.mem_perfectClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.mem_perfectClosure_iff {x : A} : x in perfectClosure R A p ↔ ex
ists n : Nat, x ^ p ^ n in (algebraMap R A).rangeS
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Subalgebra.mem_perfectClosure_iff {x : A} :
    x ∈ perfectClosure R A p ↔ ∃ n : ℕ, x ^ p ^ n ∈ (algebraMap R A).rangeS := Iff.rfl

end Subalgebra

variable {k K R : Type*} [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R]

/-
**IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar** 是 Math
lib 中的一个引理，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar [IsP
urelyInseparable k K] (q : Nat) [ExpChar k q] (x : R otimes[k] K) : exists n, x 
^ q ^ n in (algebraMap R (R otimes[k] K)).range
参数：q : Nat；x : R otimes[k] K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `expChar_is_prime_or_one`：expChar_is_prime_or_one (q : Nat) [hq : ExpChar
 R q] : Nat.Prime q ∨ q = 1
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsPurelyInseparable.pow_mem`：IsPurelyInseparable.pow_mem [IsPurelyInsepa
rable F E] : exists n : Nat, x ^ q ^ n in (algebraMap F E).range
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Algebra.TensorProduct.tmul_mul_tmul`：tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : 
B) : a₁ otimesₜ[R] b₁ * a₂ otimesₜ[R] b₂ = (a₁ * a₂) otimesₜ[R] (b₁ * b₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Algebra.TensorProduct.tmul_pow`：tmul_pow (a : A) (b : B) (k : Nat) : a o
timesₜ[R] b ^ k = (a ^ k) otimesₜ[R] (b ^ k)
· 使用定理 `Subring.mul_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) 
{x y : R}, x ∈ s → y ∈ s → x * y ∈ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `Algebra.TensorProduct.algebraMap_apply`：algebraMap_apply [SMulCommClass 
R S A] (r : S) : algebraMap S (A otimes[R] B) r = (algebraMap S A) r otimesₜ 1
· 使用引理 `Algebra.TensorProduct.tmul_one_eq_one_tmul`：tmul_one_eq_one_tmul (r : R)
 : algebraMap R A r otimesₜ[R] 1 = 1 otimesₜ algebraMap R B r
· 使用引理 `expChar_of_injective_ringHom`：expChar_of_injective_ringHom [NonAssocSemi
ring R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) (q : Nat)
 [hR : ExpChar R q…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
（共 39 条，此处仅展示前 30 条）
-/
lemma IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
    [IsPurelyInseparable k K] (q : ℕ) [ExpChar k q] (x : R ⊗[k] K) :
    ∃ n, x ^ q ^ n ∈ (algebraMap R (R ⊗[k] K)).range := by
  nontriviality (R ⊗[k] K)
  obtain (hq | hq) := expChar_is_prime_or_one k q
  induction x with
  | zero => exact ⟨0, 0, by simp⟩
  | add x y h h' =>
    have : ExpChar (R ⊗[k] K) q := expChar_of_injective_ringHom (algebraMap k _).injective q
    simp_rw [RingHom.mem_range, ← RingHom.mem_rangeS, ← Subalgebra.mem_perfectClosure_iff] at h h' ⊢
    exact add_mem h h'
  | tmul x y =>
    obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem k q y
    use n
    have : (x ^ q ^ n) ⊗ₜ[k] (y ^ q ^ n) =
        (x ^ q ^ n) ⊗ₜ[k] (1 : K) * (1 : R) ⊗ₜ[k] (y ^ q ^ n) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Algebra.TensorProduct.tmul_pow, this]
    refine Subring.mul_mem _ ⟨x ^ q ^ n, rfl⟩ ⟨algebraMap k R a, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul, ha]
  · subst hq
    have : CharZero k := charZero_of_expChar_one' k
    exact ⟨0, (Algebra.TensorProduct.includeLeft_surjective R _ <|
      IsPurelyInseparable.surjective_algebraMap_of_isSeparable k K) _⟩
/-
**IsPurelyInseparable.exists_pow_mem_range_tensorProduct** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：IsPurelyInseparable.exists_pow_mem_range_tensorProduct [IsPurelyInseparabl
e k K] (x : R otimes[k] K) : exists n > 0, x ^ n in (algebraMap R (R otimes[k] K
)).range
参数：x : R otimes[k] K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar`：I
sPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar [IsPurelyIn
separable k K] (q : Nat) [ExpChar k q] (x : R otimes[k] K) …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用引理 `expChar_is_prime_or_one`：expChar_is_prime_or_one (q : Nat) [hq : ExpChar
 R q] : Nat.Prime q ∨ q = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsPurelyInseparable.exists_pow_mem_range_tensorProduct [IsPurelyInseparable k K]
    (x : R ⊗[k] K) : ∃ n > 0, x ^ n ∈ (algebraMap R (R ⊗[k] K)).range := by
  let q := ringExpChar k
  obtain ⟨n, hr⟩ := exists_pow_pow_mem_range_tensorProduct_of_expChar q x
  refine ⟨q ^ n, pow_pos ?_ _, hr⟩
  obtain (hq | hq) := expChar_is_prime_or_one k q <;> simp [hq, Nat.Prime.pos]

end

