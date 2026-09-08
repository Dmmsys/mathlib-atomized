/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.Algebra.Algebra.Field
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.FieldTheory.Differential.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Liouville's theorem

A proof of Liouville's theorem. Follows
[Rosenlicht, M. Integration in finite terms][Rosenlicht_1972].

## Liouville field extension

This file defines Liouville field extensions, which are differential field extensions which satisfy
a slight generalization of Liouville's theorem. Note that this definition doesn't appear in the
literature, and we introduce it as part of the formalization of Liouville's theorem.

## Main declarations
- `IsLiouville`: A field extension being Liouville
- `isLiouville_of_finiteDimensional`: all finite-dimensional field extensions
  (of a field with characteristic 0) are Liouville.

-/

public section

open Differential algebraMap IntermediateField Finset Polynomial

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K] [DifferentialAlgebra F K]

/--
We say that a differential field extension `K / F` is Liouville if, whenever an element `a ∈ F` can
be written as `a = v + ∑ cᵢ * logDeriv uᵢ` for `v, cᵢ, uᵢ ∈ K` and `cᵢ` constant, it can also be
written in that way with `v, cᵢ, uᵢ ∈ F`.
-/
/-
**IsLiouville** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (K : Type u_2) → [inst : Field F] → [inst_1 : Field K] 
→ [Differential F] → [Differential K] → [Algebra F K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a differential field extension `K / F` is Liouville if, whenever an 
element `a ∈ F` can
be written as `a = v + ∑ cᵢ * logDeriv uᵢ` for `v, cᵢ, uᵢ ∈ K` and `cᵢ` constant
, it can also be
written in that way with `v, cᵢ, uᵢ ∈ F`.
-/
class IsLiouville : Prop where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
    (u : ι → K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′) :
    ∃ (ι₀ : Type) (_ : Fintype ι₀) (c₀ : ι₀ → F) (_ : ∀ x, (c₀ x)′ = 0)
      (u₀ : ι₀ → F) (v₀ : F), a = ∑ x, c₀ x * logDeriv (u₀ x) + v₀′
/-
**IsLiouville.rfl** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsLiouville.rfl : IsLiouville F F where isLiouville (a : F) (ι : Type) [Fi
ntype ι] (c : ι -> F) (hc : forall x, (c x)′ = 0) (u : ι -> F) (v : F) (h : a = 
∑ x, c x * logDeriv (u x) + v′)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsLiouville.rfl : IsLiouville F F where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → F) (v : F) (h : a = ∑ x, c x * logDeriv (u x) + v′) :=
    ⟨ι, _, c, hc, u, v, h⟩
/-
**IsLiouville.trans** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLiouville.trans {A : Type*} [Field A] [Algebra K A] [Algebra F A] [Diffe
rential A] [IsScalarTower F K A] [Differential.ContainConstants F K] (inst1 : Is
Liouville F K) (inst2 : IsLiouville K A) : IsLiouville F A where isLiouville (a 
: F) (ι : Type) [Fintype ι] (c : ι -> F) (hc : forall x, (c x)′ = 0) (u : ι -> A
) (v : A) (h : a = ∑ x, c x * logDeriv (u x) + v′)
参数：inst1 : IsLiouville F K；inst2 : IsLiouville K A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLiouville.isLiouville`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F
} {inst_1 : Field K} {inst_2 : Differential F} {inst_3 : Differential K}   {inst
_4 : Algebra …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `mem_range_of_deriv_eq_zero`：mem_range_of_deriv_eq_zero (A : Type*) {B : 
Type*} [CommRing A] [CommRing B] [Algebra A B] [Differential B] [Differential.Co
ntainConstants A…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用引理 `algebraMap.coe_deriv`：algebraMap.coe_deriv {A : Type*} {B : Type*} [Comm
Ring A] [CommRing B] [Algebra A B] [Differential A] [Differential B] [Differenti
alAlgebra …
· 使用定理 `algebraMap.coe_zero`：coe_zero : (↑(0 : R) : A) = 0
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma IsLiouville.trans {A : Type*} [Field A] [Algebra K A] [Algebra F A]
    [Differential A] [IsScalarTower F K A] [Differential.ContainConstants F K]
    (inst1 : IsLiouville F K) (inst2 : IsLiouville K A) : IsLiouville F A where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → A) (v : A) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, h₀⟩ := inst2.isLiouville (a : K) ι
        ((↑) ∘ c)
        (fun _ ↦ by simp only [Function.comp_apply, ← coe_deriv, coe_eq_zero_iff, hc])
        ((↑) ∘ u) v (by simpa only [Function.comp_apply, ← IsScalarTower.algebraMap_apply])
    have hc (x : ι₀) := mem_range_of_deriv_eq_zero F (hc₀ x)
    choose c₀ hc using hc
    apply inst1.isLiouville a ι₀ c₀ _ u₀ v₀
    · rw [h₀]
      simp [hc]
    · intro
      apply_fun ((↑) : F → K)
      · simp only [coe_deriv, hc, algebraMap.coe_zero]
        apply hc₀
      · apply FaithfulSMul.algebraMap_injective

section Algebraic
/-
The case of Liouville's theorem for algebraic extensions.
-/

variable {F K} [CharZero F]

/--
If `K` is a Liouville extension of `F` and `B` is a finite-dimensional intermediate
field `K / B / F`, then it's also a Liouville extension of `F`.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K` is a Liouville extension of `F` and `B` is a finite-dimensional intermedi
ate
field `K / B / F`, then it's also a Liouville extension of `F`.
-/
instance (B : IntermediateField F K)
    [FiniteDimensional F B] [inst : IsLiouville F K] :
    IsLiouville F B where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → B) (v : B) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    apply inst.isLiouville a ι c hc (B.val ∘ u) (B.val v)
    dsimp only [coe_val, Function.comp_apply]
    conv =>
      rhs
      congr
      · rhs
        intro x
        rhs
        apply logDeriv_algebraMap (u x)
      · apply (deriv_algebraMap v)
    simp_rw [IsScalarTower.algebraMap_apply F B K]
    norm_cast


/--
Transfer an `IsLiouville` instance using an equivalence `K ≃ₐ[F] K'`.
Requires an algebraic `K'` to show that the equivalence commutes with the derivative.
-/
/-
**IsLiouville.equiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLiouville.equiv {K' : Type*} [Field K'] [Differential K'] [Algebra F K']
 [DifferentialAlgebra F K'] [Algebra.IsAlgebraic F K'] [inst : IsLiouville F K] 
(e : K ≃ₐ[F] K') : IsLiouville F K' where isLiouville (a : F) (ι : Type) [Fintyp
e ι] (c : ι -> F) (hc : forall x, (c x)′ = 0) (u : ι -> K') (v : K') (h : a = ∑ 
x, c x * logDeriv (u x) + v′)
参数：e : K ≃ₐ[F] K'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLiouville.isLiouville`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F
} {inst_1 : Field K} {inst_2 : Differential F} {inst_3 : Differential K}   {inst
_4 : Algebra …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Differential.algEquiv_deriv'`：algEquiv_deriv' (f : R ≃ₐ[A] R') (x : R) :
 f (x′) = (f x)′
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Transfer an `IsLiouville` instance using an equivalence `K ≃ₐ[F] K'`.
Requires an algebraic `K'` to show that the equivalence commutes with the deriva
tive.
-/
lemma IsLiouville.equiv {K' : Type*} [Field K'] [Differential K'] [Algebra F K']
    [DifferentialAlgebra F K'] [Algebra.IsAlgebraic F K']
    [inst : IsLiouville F K] (e : K ≃ₐ[F] K') : IsLiouville F K' where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → K') (v : K') (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    apply inst.isLiouville a ι c hc (e.symm ∘ u) (e.symm v)
    apply_fun e.symm at h
    simpa [AlgEquiv.commutes, map_add, map_sum, map_mul, logDeriv, algEquiv_deriv'] using h

/--
A finite-dimensional Galois extension of `F` is a Liouville extension.
This is private because it's generalized by all finite-dimensional extensions being Liouville.
-/
private local instance isLiouville_of_finiteDimensional_galois [FiniteDimensional F K]
    [IsGalois F K] : IsLiouville F K where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    have : CharZero K := charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective F K)
    -- We sum `e x` over all isomorphisms `e : K ≃ₐ[F] K`.
    -- Because this is a Galois extension each of the relevant values will be in `F`.
    -- We need to divide by `Fintype.card (K ≃ₐ[F] K)` to get the original answer.
    let c₀ (i : ι) := (c i) / (Fintype.card (K ≃ₐ[F] K))
    -- logDeriv turns sums to products, so the new `u` will be the product of the old `u` over all
    -- isomorphisms
    let u₁ (i : ι) := ∏ x : (K ≃ₐ[F] K), x (u i)
    -- Each of the values of u₁ are fixed by all isomorphisms.
    have : ∀ i, u₁ i ∈ fixedField (⊤ : Subgroup (K ≃ₐ[F] K)) := by
      rintro i ⟨e, _⟩
      change e (u₁ i) = u₁ i
      simp only [u₁, map_prod]
      apply Fintype.prod_equiv (Equiv.mulLeft e)
      simp
    have ffb : fixedField ⊤ = ⊥ := (IsGalois.tfae.out 0 1).mp (inferInstance : IsGalois F K)
    simp_rw [ffb, IntermediateField.mem_bot, Set.mem_range] at this
    -- Therefore they are all in `F`. We use `choose` to get their values in `F`.
    choose u₀ hu₀ using this
    -- We do almost the same thing for `v₁`, just with sum instead of product.
    let v₁ := (∑ x : (K ≃ₐ[F] K), x v) / (Fintype.card ((K ≃ₐ[F] K)))
    have : v₁ ∈ fixedField (⊤ : Subgroup (K ≃ₐ[F] K)) := by
      rintro ⟨e, _⟩
      change e v₁ = v₁
      simp only [v₁, map_div₀, map_sum, map_natCast]
      congr 1
      apply Fintype.sum_equiv (Equiv.mulLeft e)
      simp
    rw [ffb, IntermediateField.mem_bot] at this
    obtain ⟨v₀, hv₀⟩ := this
    exists ι, inferInstance, c₀, ?_, u₀, v₀
    · -- We need to prove that all `c₀` are constants.
      -- This is true because they are the division of a constant by
      -- a natural number (which is also constant)
      intro x
      simp [c₀, Derivation.leibniz_div, hc]
    · -- Proving that this works is mostly straightforward algebraic manipulation,
      apply_fun (algebraMap F K)
      case inj =>
        exact FaithfulSMul.algebraMap_injective F K
      simp only [map_add, map_sum, map_mul, ← logDeriv_algebraMap, hu₀, ← deriv_algebraMap, hv₀]
      unfold u₁ v₁ c₀
      clear c₀ u₁ u₀ hu₀ v₁ v₀ hv₀
      push_cast
      rw [Derivation.leibniz_div_const, smul_eq_mul, inv_mul_eq_div]
      case h => simp
      simp only [map_sum, div_mul_eq_mul_div]
      rw [← sum_div, ← add_div]
      field_simp
      -- Here we rewrite logDeriv (∏ x : K ≃ₐ[F] K, x (u i)) to ∑ x : K ≃ₐ[F] K, logDeriv (x (u i))
      conv =>
        enter [2, 1, 2, i, 2]
        equals ∑ x : K ≃ₐ[F] K, logDeriv (x (u i)) =>
          by_cases h : u i = 0 <;>
          simp [logDeriv_prod, h]
      simp_rw [mul_sum]
      rw [sum_comm, ← sum_add_distrib]
      trans ∑ _ : (K ≃ₐ[F] K), a
      · simp [mul_comm]
      · rcongr e
        apply_fun e at h
        simp only [AlgEquiv.commutes, map_add, map_sum, map_mul] at h
        convert! h using 2
        · rcongr x
          simp [logDeriv, algEquiv_deriv']
        · rw [algEquiv_deriv']

/--
We lift `isLiouville_of_finiteDimensional_galois` to non-Galois field extensions by using it for the
normal closure then obtaining it for `F`.
-/
/-
**isLiouville_of_finiteDimensional** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isLiouville_of_finiteDimensional [FiniteDimensional F K] : IsLiouville F K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Algebra.IsSeparable.of_integral`：∀ (F : Type u_1) [inst : Field F] (K : 
Type u_2) [inst_1 : Ring K] [inst_2 : Algebra F K] [IsDomain K]   [Algebra.IsInt
egral F K] [CharZero …
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IntermediateField.le_normalClosure`：le_normalClosure : K <= normalClosur
e F K L
· 使用引理 `IsLiouville.equiv`：IsLiouville.equiv {K' : Type*} [Field K'] [Differenti
al K'] [Algebra F K'] [DifferentialAlgebra F K'] [Algebra.IsAlgebraic F K'] [ins
t : IsL…
· 使用定理 `Differential.instDifferentialAlgebraSubtypeMemIntermediateField`：∀ {F : 
Type u_2} [inst : Field F] [inst_1 : Differential F] [inst_2 : CharZero F] {K : 
Type u_3} [inst_3 : Field K]   [inst_4 : Algebra F K]…
· 使用定理 `instIsLiouvilleSubtypeMemIntermediateField`：∀ {F : Type u_1} {K : Type u
_2} [inst : Field F] [inst_1 : Field K] [inst_2 : Differential F] [inst_3 : Diff
erential K]   [inst_4 : Algebra …
· 使用定理 `_private.Mathlib.FieldTheory.Differential.Liouville.0.isLiouville_of_fin
iteDimensional_galois`：∀ {F : Type u_1} {K : Type u_2} [inst : Field F] [inst_1 
: Field K] [inst_2 : Differential F] [inst_3 : Differential K]   [inst_4 : Algeb
ra …
· 使用定理 `IsAlgClosure.isGalois`：∀ (k : Type u_1) (K : Type u_2) [inst : Field k] 
[inst_1 : Field K] [inst_2 : Algebra k K] [IsAlgClosure k K]   [CharZero k], IsG
alois k K
· 使用定理 `AlgebraicClosure.instIsAlgClosureOfIsAlgebraic`：∀ (k : Type u) [inst : F
ield k] {L : Type u_1} [inst_1 : Field L] [inst_2 : Algebra k L] [Algebra.IsAlge
braic k L],   IsAlgClosure k (Algebr…
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K

--- 原说明 ---
We lift `isLiouville_of_finiteDimensional_galois` to non-Galois field extensions
 by using it for the
normal closure then obtaining it for `F`.
-/
instance isLiouville_of_finiteDimensional [FiniteDimensional F K] :
    IsLiouville F K :=
  let map := IsAlgClosed.lift (M := AlgebraicClosure F) (R := F) (S := K)
  let K' := map.fieldRange
  have : FiniteDimensional F K' :=
    LinearMap.finiteDimensional_range map.toLinearMap
  let K'' := normalClosure F K' (AlgebraicClosure F)
  let B : IntermediateField F K'' := IntermediateField.restrict
    (F := K') (IntermediateField.le_normalClosure ..)
  have kequiv : K ≃ₐ[F] ↥B := (show K ≃ₐ[F] K' from AlgEquiv.ofInjectiveField map).trans
    (IntermediateField.restrictAlgEquiv _)
  IsLiouville.equiv kequiv.symm

end Algebraic

