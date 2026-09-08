/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Algebraic Independence

This file contains basic results on algebraic independence of a family of elements of an `R`-algebra

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## Tags
transcendence basis, transcendence degree, transcendence

-/

@[expose] public section


noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

universe u v v'

variable {ι : Type u} {ι' R : Type*} {A : Type v} {A' : Type v'} {x : ι → A}
variable [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']

variable (R A) in
/-- The transcendence degree of a commutative algebra `A` over a commutative ring `R` is
defined to be the maximal cardinality of an `R`-algebraically independent set in `A`. -/
/-
**Algebra.trdeg** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_2) → (A : Type v) → [inst : CommRing R] → [inst_1 : CommRing A
] → [Algebra R A] → Cardinal.{v}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transcendence degree of a commutative algebra `A` over a commutative ring `R
` is
defined to be the maximal cardinality of an `R`-algebraically independent set in
 `A`.
-/
@[stacks 030G] def Algebra.trdeg : Cardinal.{v} :=
  ⨆ ι : { s : Set A // AlgebraicIndepOn R _root_.id s }, Cardinal.mk ι.1
/-
**algebraicIndependent_iff_ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_iff_ker_eq_bot : AlgebraicIndependent R x ↔ RingHom.k
er (MvPolynomial.aeval x : MvPolynomial ι R ->ₐ[R] A).toRingHom = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem algebraicIndependent_iff_ker_eq_bot :
    AlgebraicIndependent R x ↔
      RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] A).toRingHom = ⊥ :=
  RingHom.injective_iff_ker_eq_bot _

@[simp]
/-
**algebraicIndependent_empty_type_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_empty_type_iff [IsEmpty ι] : AlgebraicIndependent R x
 ↔ Injective (algebraMap R A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraicIndependent_iff_injective_aeval`：algebraicIndependent_iff_injec
tive_aeval : AlgebraicIndependent R x ↔ Injective (MvPolynomial.aeval x : MvPoly
nomial ι R ->ₐ[R] A)
· 使用引理 `MvPolynomial.aeval_injective_iff_of_isEmpty`：aeval_injective_iff_of_isEm
pty [CommSemiring S₁] [Algebra R S₁] {f : σ -> S₁} : Function.Injective (aeval f
 : MvPolynomial σ R ->ₐ[R] S₁) ↔ …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem algebraicIndependent_empty_type_iff [IsEmpty ι] :
    AlgebraicIndependent R x ↔ Injective (algebraMap R A) := by
  rw [algebraicIndependent_iff_injective_aeval, MvPolynomial.aeval_injective_iff_of_isEmpty]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FaithfulSMul R A] : Nonempty { s : Set A // AlgebraicIndepOn R id s } :=
  ⟨∅, algebraicIndependent_empty_type_iff.mpr <| FaithfulSMul.algebraMap_injective R A⟩

namespace AlgebraicIndependent

variable (hx : AlgebraicIndependent R x)
include hx

/-
**AlgebraicIndependent.algebraMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Independent`。
形式化陈述：algebraMap_injective : Injective (algebraMap R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} {f : α → β},   Function.Injective f → ∀ (g : γ → α), Function.Injective (
f ∘ g) ↔ Function.In…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `algebraicIndependent_iff_injective_aeval`：algebraicIndependent_iff_injec
tive_aeval : AlgebraicIndependent R x ↔ Injective (MvPolynomial.aeval x : MvPoly
nomial ι R ->ₐ[R] A)
· 使用定理 `MvPolynomial.C_injective`：C_injective (σ : Type*) (R : Type*) [CommSemir
ing R] : Function.Injective (C : R -> MvPolynomial σ R)
-/
theorem algebraMap_injective : Injective (algebraMap R A) := by
  simpa [Function.comp_def] using
    (Injective.of_comp_iff (algebraicIndependent_iff_injective_aeval.1 hx) MvPolynomial.C).2
      (MvPolynomial.C_injective _ _)
/-
**AlgebraicIndependent.linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicInd
ependent`。
形式化陈述：linearIndependent : LinearIndependent R x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff_injective_finsuppLinearCombination`：linearIndepend
ent_iff_injective_finsuppLinearCombination : LinearIndependent R v ↔ Injective (
Finsupp.linearCombination R v)
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `algebraicIndependent_iff_injective_aeval`：algebraicIndependent_iff_injec
tive_aeval : AlgebraicIndependent R x ↔ Injective (MvPolynomial.aeval x : MvPoly
nomial ι R ->ₐ[R] A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.linearIndependent_X`：linearIndependent_X : LinearIndependen
t R (X : σ -> MvPolynomial σ R)
-/
theorem linearIndependent : LinearIndependent R x := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  have : Finsupp.linearCombination R x =
      (MvPolynomial.aeval x).toLinearMap.comp (Finsupp.linearCombination R X) := by
    ext
    simp
  rw [this]
  refine (algebraicIndependent_iff_injective_aeval.mp hx).comp ?_
  rw [← linearIndependent_iff_injective_finsuppLinearCombination]
  exact linearIndependent_X _ _
/-
**AlgebraicIndependent.injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIndependent
`。
形式化陈述：∀ {ι : Type u} {R : Type u_2} {A : Type v} {x : ι → A} [inst : CommRing R]
 [inst_1 : CommRing A] [inst_2 : Algebra R A],   AlgebraicIndependent R x → ∀ [N
ontrivial R], Function.Injective x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `AlgebraicIndependent.linearIndependent`：linearIndependent : LinearIndepe
ndent R x
-/
protected theorem injective [Nontrivial R] : Injective x :=
  hx.linearIndependent.injective
/-
**AlgebraicIndependent.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIndependent`。
形式化陈述：ne_zero [Nontrivial R] (i : ι) : x i != 0
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `AlgebraicIndependent.linearIndependent`：linearIndependent : LinearIndepe
ndent R x
-/
theorem ne_zero [Nontrivial R] (i : ι) : x i ≠ 0 :=
  hx.linearIndependent.ne_zero i
/-
**AlgebraicIndependent.map** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIndependent`。
形式化陈述：map {f : A ->ₐ[R] A'} (hf_inj : Set.InjOn f (adjoin R (range x))) : Algebr
aicIndependent R (f ∘ x)
参数：hf_inj : Set.InjOn f (adjoin R (range x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgHom.mem_range`：mem_range (φ : A ->ₐ[R] B) {y : B} : y in φ.range ↔ ex
ists x, φ x = y
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.aeval_rename`：aeval_rename [Algebra R S] : aeval g (rename 
k p) = aeval (g ∘ k) p
· 使用定理 `Algebra.adjoin_eq_range`：∀ (R : Type u) {S₁ : Type v} [inst : CommSemiri
ng R] [inst_1 : CommSemiring S₁] [inst_2 : Algebra R S₁] (s : Set S₁),   Algebra
.adjoin R s =…
-/
theorem map {f : A →ₐ[R] A'} (hf_inj : Set.InjOn f (adjoin R (range x))) :
    AlgebraicIndependent R (f ∘ x) := by
  have : aeval (f ∘ x) = f.comp (aeval x) := by ext; simp
  have h : ∀ p : MvPolynomial ι R, aeval x p ∈ (@aeval R _ _ _ _ _ ((↑) : range x → A)).range := by
    intro p
    rw [AlgHom.mem_range]
    refine ⟨MvPolynomial.rename (codRestrict x (range x) mem_range_self) p, ?_⟩
    simp [Function.comp_def, aeval_rename]
  intro x y hxy
  rw [this] at hxy
  rw [adjoin_eq_range] at hf_inj
  exact hx (hf_inj (h x) (h y) hxy)
/-
**AlgebraicIndependent.map'** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIndependent`。
形式化陈述：map' {f : A ->ₐ[R] A'} (hf_inj : Injective f) : AlgebraicIndependent R (f 
∘ x)
参数：hf_inj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.map`：map {f : A ->ₐ[R] A'} (hf_inj : Set.InjOn f (a
djoin R (range x))) : AlgebraicIndependent R (f ∘ x)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem map' {f : A →ₐ[R] A'} (hf_inj : Injective f) : AlgebraicIndependent R (f ∘ x) :=
  hx.map hf_inj.injOn

/-- If `x = {x_i : A | i : ι}` and `f = {f_i : MvPolynomial ι R | i : ι}` are algebraically
independent over `R`, then `{f_i(x) | i : ι}` is also algebraically independent over `R`.
For the partial converse, see `AlgebraicIndependent.of_aeval`. -/
/-
**AlgebraicIndependent.aeval_of_algebraicIndependent** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicIndependent`。
形式化陈述：aeval_of_algebraicIndependent {f : ι -> MvPolynomial ι R} (hf : AlgebraicI
ndependent R f) : AlgebraicIndependent R fun i => aeval x (f i)
参数：hf : AlgebraicIndependent R f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraicIndependent_iff`：algebraicIndependent_iff : AlgebraicIndependen
t R x ↔ forall p : MvPolynomial ι R, MvPolynomial.aeval (x : ι -> A) p = 0 -> p 
= 0
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.aeval_comp_bind₁`：aeval_comp_bind₁ [Algebra R S] (f : τ -> 
S) (g : σ -> MvPolynomial τ R) : (aeval f).comp (bind₁ g) = aeval fun i => aeval
 f (g i)

--- 原说明 ---
If `x = {x_i : A | i : ι}` and `f = {f_i : MvPolynomial ι R | i : ι}` are algebr
aically
independent over `R`, then `{f_i(x) | i : ι}` is also algebraically independent 
over `R`.
For the partial converse, see `AlgebraicIndependent.of_aeval`.
-/
theorem aeval_of_algebraicIndependent
    {f : ι → MvPolynomial ι R} (hf : AlgebraicIndependent R f) :
    AlgebraicIndependent R fun i ↦ aeval x (f i) := by
  rw [algebraicIndependent_iff] at hx hf ⊢
  intro p hp
  exact hf _ (hx _ (by rwa [← aeval_comp_bind₁, AlgHom.comp_apply] at hp))

omit hx in
/-- If `{f_i(x) | i : ι}` is algebraically independent over `R`, then
`{f_i : MvPolynomial ι R | i : ι}` is also algebraically independent over `R`.
In fact, the `x = {x_i : A | i : ι}` is also transcendental over `R` provided that `R`
is a field and `ι` is finite; the proof needs transcendence degree. -/
/-
**AlgebraicIndependent.of_aeval** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIndependent`
。
形式化陈述：of_aeval {f : ι -> MvPolynomial ι R} (H : AlgebraicIndependent R fun i => 
aeval x (f i)) : AlgebraicIndependent R f
参数：H : AlgebraicIndependent R fun i => aeval x (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraicIndependent_iff`：algebraicIndependent_iff : AlgebraicIndependen
t R x ↔ forall p : MvPolynomial ι R, MvPolynomial.aeval (x : ι -> A) p = 0 -> p 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.aeval_comp_bind₁`：aeval_comp_bind₁ [Algebra R S] (f : τ -> 
S) (g : σ -> MvPolynomial τ R) : (aeval f).comp (bind₁ g) = aeval fun i => aeval
 f (g i)
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
· 使用定理 `MvPolynomial.bind₁.eq_1`：∀ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} 
[inst : CommSemiring R] (f : σ → MvPolynomial τ R),   MvPolynomial.bind₁ f = MvP
olynomial.aev…
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

--- 原说明 ---
If `{f_i(x) | i : ι}` is algebraically independent over `R`, then
`{f_i : MvPolynomial ι R | i : ι}` is also algebraically independent over `R`.
In fact, the `x = {x_i : A | i : ι}` is also transcendental over `R` provided th
at `R`
is a field and `ι` is finite; the proof needs transcendence degree.
-/
theorem of_aeval {f : ι → MvPolynomial ι R}
    (H : AlgebraicIndependent R fun i ↦ aeval x (f i)) :
    AlgebraicIndependent R f := by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
  exact H p (by rw [← aeval_comp_bind₁, AlgHom.comp_apply, bind₁, hp, map_zero])

end AlgebraicIndependent

/-
**isEmpty_algebraicIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_algebraicIndependent (h : ¬ Injective (algebraMap R A)) : IsEmpty 
{ s : Set A // AlgebraicIndepOn R id s } where false s
参数：h : ¬ Injective (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.algebraMap_injective`：algebraMap_injective : Inject
ive (algebraMap R A)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem isEmpty_algebraicIndependent (h : ¬ Injective (algebraMap R A)) :
    IsEmpty { s : Set A // AlgebraicIndepOn R id s } where
  false s := h s.2.algebraMap_injective
/-
**trdeg_eq_zero_of_not_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trdeg_eq_zero_of_not_injective (h : ¬ Injective (algebraMap R A)) : trdeg 
R A = 0
参数：h : ¬ Injective (algebraMap R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_algebraicIndependent`：isEmpty_algebraicIndependent (h : ¬ Inject
ive (algebraMap R A)) : IsEmpty { s : Set A // AlgebraicIndepOn R id s } where f
alse s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.trdeg.eq_1`：∀ (R : Type u_2) (A : Type v) [inst : CommRing R] [i
nst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.trdeg R A = ⨆ ι, Cardinal.
mk ↑↑ι
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem trdeg_eq_zero_of_not_injective (h : ¬ Injective (algebraMap R A)) : trdeg R A = 0 := by
  have := isEmpty_algebraicIndependent h
  rw [trdeg, ciSup_of_empty, bot_eq_zero]
/-
**MvPolynomial.algebraicIndependent_X** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MvPolynomial.algebraicIndependent_X (σ R : Type*) [CommRing R] : Algebraic
Independent R (X (R
参数：σ R : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicIndependent.eq_1`：∀ {ι : Type u_1} (R : Type u_3) {A : Type u_5
} (x : ι → A) [inst : CommRing R] [inst_1 : CommRing A]   [inst_2 : Algebra R A]
, AlgebraicInde…
· 使用定理 `MvPolynomial.aeval_X_left`：aeval_X_left : aeval X = AlgHom.id R (MvPolyn
omial σ R)
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
theorem MvPolynomial.algebraicIndependent_X (σ R : Type*) [CommRing R] :
    AlgebraicIndependent R (X (R := R) (σ := σ)) := by
  rw [AlgebraicIndependent, aeval_X_left]
  exact injective_id

open AlgebraicIndependent
/-
**AlgHom.algebraicIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.algebraicIndependent_iff (f : A ->ₐ[R] A') (hf : Injective f) : Alg
ebraicIndependent R (f ∘ x) ↔ AlgebraicIndependent R x
参数：f : A ->ₐ[R] A'；hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.of_comp`：of_comp (f : A ->ₐ[R] A') (hfv : Algebraic
Independent R (f ∘ x)) : AlgebraicIndependent R x
· 使用定理 `AlgebraicIndependent.map`：map {f : A ->ₐ[R] A'} (hf_inj : Set.InjOn f (a
djoin R (range x))) : AlgebraicIndependent R (f ∘ x)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem AlgHom.algebraicIndependent_iff (f : A →ₐ[R] A') (hf : Injective f) :
    AlgebraicIndependent R (f ∘ x) ↔ AlgebraicIndependent R x :=
  ⟨fun h => h.of_comp f, fun h => h.map hf.injOn⟩

@[nontriviality]
/-
**AlgebraicIndependent.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.of_subsingleton [Subsingleton R] : AlgebraicIndepende
nt R x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `algebraicIndependent_iff`：algebraicIndependent_iff : AlgebraicIndependen
t R x ↔ forall p : MvPolynomial ι R, MvPolynomial.aeval (x : ι -> A) p = 0 -> p 
= 0
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem AlgebraicIndependent.of_subsingleton [Subsingleton R] : AlgebraicIndependent R x :=
  algebraicIndependent_iff.2 fun _ _ => Subsingleton.elim _ _
/-
**isTranscendenceBasis_iff_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTranscendenceBasis_iff_of_subsingleton [Subsingleton R] (x : ι -> A) : I
sTranscendenceBasis R x ↔ Nonempty ι
参数：x : ι -> A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AlgebraicIndependent.of_subsingleton`：AlgebraicIndependent.of_subsinglet
on [Subsingleton R] : AlgebraicIndependent R x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem isTranscendenceBasis_iff_of_subsingleton [Subsingleton R] (x : ι → A) :
    IsTranscendenceBasis R x ↔ Nonempty ι := by
  have := Module.subsingleton R A
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨.of_subsingleton, fun s hs hx ↦
    hx.antisymm fun a _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim ..⟩⟩⟩
  by_contra! hι
  have := h.2 {0} .of_subsingleton
  simp [range_eq_empty, eq_comm (a := ∅)] at this
/-
**IsTranscendenceBasis.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `IsTranscendenc
eBasis`。
形式化陈述：∀ {ι : Type u} {R : Type u_2} {A : Type v} {x : ι → A} [inst : CommRing R]
 [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Subsingleton R] [Nonempty ι], I
sTranscendenceBasis R x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isTranscendenceBasis_iff_of_subsingleton`：isTranscendenceBasis_iff_of_su
bsingleton [Subsingleton R] (x : ι -> A) : IsTranscendenceBasis R x ↔ Nonempty ι
-/
@[nontriviality] theorem IsTranscendenceBasis.of_subsingleton [Subsingleton R] [Nonempty ι] :
    IsTranscendenceBasis R x :=
  (isTranscendenceBasis_iff_of_subsingleton x).mpr ‹_›
/-
**trdeg_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_2} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [i
nst_2 : Algebra R A] [Subsingleton R],   Algebra.trdeg R A = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `Set.subsingleton_of_subsingleton`：subsingleton_of_subsingleton [Subsingl
eton α] {s : Set α} : s.Subsingleton
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicIndependent.of_subsingleton`：AlgebraicIndependent.of_subsinglet
on [Subsingleton R] : AlgebraicIndependent R x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
@[nontriviality] theorem trdeg_subsingleton [Subsingleton R] : trdeg R A = 1 :=
  have := Module.subsingleton R A
  (ciSup_le' fun s ↦ by simpa using Set.subsingleton_of_subsingleton).antisymm <| le_ciSup_of_le
    Cardinal.bddAbove_of_small ⟨{0}, .of_subsingleton⟩ (by simp)
/-
**algebraicIndependent_adjoin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_adjoin (hs : AlgebraicIndependent R x) : @AlgebraicIn
dependent ι R (adjoin R (range x)) (fun i : ι => ⟨x i, subset_adjoin (mem_range_
self i)⟩) _ _ _
参数：hs : AlgebraicIndependent R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.of_comp`：of_comp (f : A ->ₐ[R] A') (hfv : Algebraic
Independent R (f ∘ x)) : AlgebraicIndependent R x
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem algebraicIndependent_adjoin (hs : AlgebraicIndependent R x) :
    @AlgebraicIndependent ι R (adjoin R (range x))
      (fun i : ι => ⟨x i, subset_adjoin (mem_range_self i)⟩) _ _ _ :=
  AlgebraicIndependent.of_comp (adjoin R (range x)).val hs

/-- A set of algebraically independent elements in an algebra `A` over a ring `K` is also
algebraically independent over a subring `R` of `K`. -/
/-
**AlgebraicIndependent.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.restrictScalars {K : Type*} [CommRing K] [Algebra R K
] [Algebra K A] [IsScalarTower R K A] (hinj : Function.Injective (algebraMap R K
)) (ai : AlgebraicIndependent K x) : AlgebraicIndependent R x
参数：hinj : Function.Injective (algebraMap R K)；ai : AlgebraicIndependent K x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ringHom_ext'`：ringHom_ext' {A : Type*} [Semiring A] {f g : 
MvPolynomial σ R ->+* A} (hC : f.comp C = g.comp C) (hX : forall i, f (X i) = g 
(X i)) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.coe_comp`：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp
 hmn : α -> γ) = hnp ∘ hmn
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)

--- 原说明 ---
A set of algebraically independent elements in an algebra `A` over a ring `K` is
 also
algebraically independent over a subring `R` of `K`.
-/
theorem AlgebraicIndependent.restrictScalars {K : Type*} [CommRing K] [Algebra R K] [Algebra K A]
    [IsScalarTower R K A] (hinj : Function.Injective (algebraMap R K))
    (ai : AlgebraicIndependent K x) : AlgebraicIndependent R x := by
  have : (aeval x : MvPolynomial ι K →ₐ[K] A).toRingHom.comp (MvPolynomial.map (algebraMap R K)) =
      (aeval x : MvPolynomial ι R →ₐ[R] A).toRingHom := by
    ext <;> simp [algebraMap_eq_smul_one]
  change Injective (aeval x).toRingHom
  rw [← this, RingHom.coe_comp]
  exact Injective.comp ai (MvPolynomial.map_injective _ hinj)

section RingHom

variable {S B FRS FAB : Type*} [CommRing S] [CommRing B] [Algebra S B]

section

variable [FunLike FRS R S] [RingHomClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB)

/-
**AlgebraicIndependent.of_ringHom_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.of_ringHom_of_comp_eq (H : AlgebraicIndependent S (g 
∘ x)) (hf : Function.Injective f) (h : RingHom.comp (algebraMap S B) f = RingHom
.comp g (algebraMap R A)) : AlgebraicIndependent R x
参数：H : AlgebraicIndependent S (g ∘ x)；hf : Function.Injective f；h : RingHom.comp
 (algebraMap S B) f = RingHom.comp g (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraicIndependent_iff`：algebraicIndependent_iff : AlgebraicIndependen
t R x ↔ forall p : MvPolynomial ι R, MvPolynomial.aeval (x : ι -> A) p = 0 -> p 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.aeval_eq_eval₂Hom`：aeval_eq_eval₂Hom (p : MvPolynomial σ R)
 : aeval f p = eval₂Hom (algebraMap R S₁) f p
· 使用定理 `MvPolynomial.eval₂Hom_map_hom`：eval₂Hom_map_hom [CommSemiring S₂] (f : R
 ->+* S₁) (g : σ -> S₂) (φ : S₁ ->+* S₂) (p : MvPolynomial σ R) : eval₂Hom φ g (
map f p) = eval₂Hom…
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
-/
theorem AlgebraicIndependent.of_ringHom_of_comp_eq (H : AlgebraicIndependent S (g ∘ x))
    (hf : Function.Injective f)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    AlgebraicIndependent R x := by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
  have := H (p.map f) <| by
    have : (g : A →+* B) _ = _ := congr(g $hp)
    rwa [map_zero, map_aeval, ← h, ← eval₂Hom_map_hom, ← aeval_eq_eval₂Hom] at this
  exact map_injective (f : R →+* S) hf (by rwa [map_zero])
/-
**AlgebraicIndependent.ringHom_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.ringHom_of_comp_eq (H : AlgebraicIndependent R x) (hf
 : Function.Surjective f) (hg : Function.Injective g) (h : RingHom.comp (algebra
Map S B) f = RingHom.comp g (algebraMap R A)) : AlgebraicIndependent S (g ∘ x)
参数：H : AlgebraicIndependent R x；hf : Function.Surjective f；hg : Function.Injecti
ve g；h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraicIndependent_iff`：algebraicIndependent_iff : AlgebraicIndependen
t R x ↔ forall p : MvPolynomial ι R, MvPolynomial.aeval (x : ι -> A) p = 0 -> p 
= 0
· 使用定理 `MvPolynomial.map_surjective`：map_surjective (hf : Function.Surjective f)
 : Function.Surjective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `MvPolynomial.eval₂Hom_map_hom`：eval₂Hom_map_hom [CommSemiring S₂] (f : R
 ->+* S₁) (g : σ -> S₂) (φ : S₁ ->+* S₂) (p : MvPolynomial σ R) : eval₂Hom φ g (
map f p) = eval₂Hom…
· 使用定理 `MvPolynomial.aeval_eq_eval₂Hom`：aeval_eq_eval₂Hom (p : MvPolynomial σ R)
 : aeval f p = eval₂Hom (algebraMap R S₁) f p
-/
theorem AlgebraicIndependent.ringHom_of_comp_eq (H : AlgebraicIndependent R x)
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    AlgebraicIndependent S (g ∘ x) := by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
  obtain ⟨q, rfl⟩ := map_surjective (f : R →+* S) hf p
  rw [H q (hg (by rwa [map_zero, ← RingHom.coe_coe g, map_aeval, ← h, ← eval₂Hom_map_hom,
    ← aeval_eq_eval₂Hom])), map_zero]

end

section

variable [EquivLike FRS R S] [RingEquivClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB)

/-
**algebraicIndependent_ringHom_iff_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_ringHom_iff_of_comp_eq (hg : Function.Injective g) (h
 : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) : Algebrai
cIndependent S (g ∘ x) ↔ AlgebraicIndependent R x
参数：hg : Function.Injective g；h : RingHom.comp (algebraMap S B) f = RingHom.comp 
g (algebraMap R A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `AlgebraicIndependent.of_ringHom_of_comp_eq`：AlgebraicIndependent.of_ring
Hom_of_comp_eq (H : AlgebraicIndependent S (g ∘ x)) (hf : Function.Injective f) 
(h : RingHom.comp (algebraMap S …
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
· 使用定理 `AlgebraicIndependent.ringHom_of_comp_eq`：AlgebraicIndependent.ringHom_of
_comp_eq (H : AlgebraicIndependent R x) (hf : Function.Surjective f) (hg : Funct
ion.Injective g) (h : RingHom…
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
theorem algebraicIndependent_ringHom_iff_of_comp_eq
    (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    AlgebraicIndependent S (g ∘ x) ↔ AlgebraicIndependent R x :=
  ⟨fun H ↦ H.of_ringHom_of_comp_eq f g (EquivLike.injective f) h,
    fun H ↦ H.ringHom_of_comp_eq f g (EquivLike.surjective f) hg h⟩

end

end RingHom

/-- Every finite subset of an algebraically independent set is algebraically independent. -/
/-
**algebraicIndependent_finset_map_embedding_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：algebraicIndependent_finset_map_embedding_subtype (s : Set A) (li : Algebr
aicIndependent R ((↑) : s -> A)) (t : Finset s) : AlgebraicIndependent R ((↑) : 
Finset.map (Embedding.subtype (· in s)) t -> A)
参数：s : Set A；li : AlgebraicIndependent R ((↑) : s -> A)；t : Finset s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicIndependent.comp`：comp (f : ι' -> ι) (hf : Function.Injective f
) : AlgebraicIndependent R (x ∘ f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Every finite subset of an algebraically independent set is algebraically indepen
dent.
-/
theorem algebraicIndependent_finset_map_embedding_subtype (s : Set A)
    (li : AlgebraicIndependent R ((↑) : s → A)) (t : Finset s) :
    AlgebraicIndependent R ((↑) : Finset.map (Embedding.subtype (· ∈ s)) t → A) := by
  let f : t.map (Embedding.subtype (· ∈ s)) → s := fun x =>
    ⟨x.1, by
      obtain ⟨x, h⟩ := x
      rw [Finset.mem_map] at h
      obtain ⟨a, _, rfl⟩ := h
      simp only [Subtype.coe_prop, Embedding.coe_subtype]⟩
  convert! AlgebraicIndependent.comp li f _
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  rw [Finset.mem_map] at hx hy
  obtain ⟨a, _, rfl⟩ := hx
  obtain ⟨b, _, rfl⟩ := hy
  simp only [f, imp_self, Subtype.mk_eq_mk]

/-- If every finite set of algebraically independent element has cardinality at most `n`,
then the same is true for arbitrary sets of algebraically independent elements. -/
/-
**algebraicIndependent_bounded_of_finset_algebraicIndependent_bounded** 是 Mathli
b 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_bounded_of_finset_algebraicIndependent_bounded {n : N
at} (H : forall s : Finset A, (AlgebraicIndependent R fun i : s => (i : A)) -> s
.card <= n) : forall s : Set A, AlgebraicIndependent R ((↑) : s -> A) -> Cardina
l.mk s <= n
参数：H : forall s : Finset A, (AlgebraicIndependent R fun i : s => (i : A)) -> s.c
ard <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.card_le_of`：card_le_of {α : Type u} {n : Nat} (H : forall s : F
inset α, s.card <= n) : #α <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `algebraicIndependent_finset_map_embedding_subtype`：algebraicIndependent_
finset_map_embedding_subtype (s : Set A) (li : AlgebraicIndependent R ((↑) : s -
> A)) (t : Finset s) : AlgebraicIndepen…

--- 原说明 ---
If every finite set of algebraically independent element has cardinality at most
 `n`,
then the same is true for arbitrary sets of algebraically independent elements.
-/
theorem algebraicIndependent_bounded_of_finset_algebraicIndependent_bounded {n : ℕ}
    (H : ∀ s : Finset A, (AlgebraicIndependent R fun i : s => (i : A)) → s.card ≤ n) :
    ∀ s : Set A, AlgebraicIndependent R ((↑) : s → A) → Cardinal.mk s ≤ n := by
  intro s li
  apply Cardinal.card_le_of
  intro t
  rw [← Finset.card_map (Embedding.subtype (· ∈ s))]
  apply H
  apply algebraicIndependent_finset_map_embedding_subtype _ li

section Subtype

/-
**AlgebraicIndependent.restrict_of_comp_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.restrict_of_comp_subtype {s : Set ι} (hs : AlgebraicI
ndependent R (x ∘ (↑) : s -> A)) : AlgebraicIndependent R (s.domRestrict x)
参数：hs : AlgebraicIndependent R (x ∘ (↑) : s -> A)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AlgebraicIndependent.restrict_of_comp_subtype {s : Set ι}
    (hs : AlgebraicIndependent R (x ∘ (↑) : s → A)) : AlgebraicIndependent R (s.domRestrict x) :=
  hs

variable (R A)
/-
**algebraicIndependent_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_empty_iff : AlgebraicIndependent R ((↑) : (∅ : Set A)
 -> A) ↔ Injective (algebraMap R A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem algebraicIndependent_empty_iff :
    AlgebraicIndependent R ((↑) : (∅ : Set A) → A) ↔ Injective (algebraMap R A) := by simp

end Subtype

/-
**AlgebraicIndependent.to_subtype_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.to_subtype_range (hx : AlgebraicIndependent R x) : Al
gebraicIndependent R ((↑) : range x -> A)
参数：hx : AlgebraicIndependent R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraicIndependent_subtype_range`：algebraicIndependent_subtype_range {
ι} {f : ι -> A} (hf : Injective f) : AlgebraicIndependent R ((↑) : range f -> A)
 ↔ AlgebraicIndependent …
· 使用定理 `AlgebraicIndependent.injective`：∀ {ι : Type u} {R : Type u_2} {A : Type 
v} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],
   AlgebraicIndepend…
-/
theorem AlgebraicIndependent.to_subtype_range (hx : AlgebraicIndependent R x) :
    AlgebraicIndependent R ((↑) : range x → A) := by
  nontriviality R
  rwa [algebraicIndependent_subtype_range hx.injective]
/-
**AlgebraicIndependent.to_subtype_range'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.to_subtype_range' (hx : AlgebraicIndependent R x) {t}
 (ht : range x = t) : AlgebraicIndependent R ((↑) : t -> A)
参数：hx : AlgebraicIndependent R x；ht : range x = t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.to_subtype_range`：AlgebraicIndependent.to_subtype_r
ange (hx : AlgebraicIndependent R x) : AlgebraicIndependent R ((↑) : range x -> 
A)
-/
theorem AlgebraicIndependent.to_subtype_range' (hx : AlgebraicIndependent R x) {t}
    (ht : range x = t) : AlgebraicIndependent R ((↑) : t → A) :=
  ht ▸ hx.to_subtype_range
/-
**IsTranscendenceBasis.to_subtype_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.to_subtype_range (hx : IsTranscendenceBasis R x) : Is
TranscendenceBasis R ((↑) : range x -> A)
参数：hx : IsTranscendenceBasis R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isTranscendenceBasis_iff_of_subsingleton`：isTranscendenceBasis_iff_of_su
bsingleton [Subsingleton R] (x : ι -> A) : IsTranscendenceBasis R x ↔ Nonempty ι
· 使用定理 `isTranscendenceBasis_subtype_range`：isTranscendenceBasis_subtype_range {
ι} {f : ι -> A} (hf : Injective f) : IsTranscendenceBasis R ((↑) : range f -> A)
 ↔ IsTranscendenceBasis …
· 使用定理 `AlgebraicIndependent.injective`：∀ {ι : Type u} {R : Type u_2} {A : Type 
v} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],
   AlgebraicIndepend…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsTranscendenceBasis.to_subtype_range (hx : IsTranscendenceBasis R x) :
    IsTranscendenceBasis R ((↑) : range x → A) := by
  cases subsingleton_or_nontrivial R
  · rw [isTranscendenceBasis_iff_of_subsingleton] at hx ⊢; infer_instance
  · rwa [isTranscendenceBasis_subtype_range hx.1.injective]
/-
**IsTranscendenceBasis.to_subtype_range'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.to_subtype_range' (hx : IsTranscendenceBasis R x) {t}
 (ht : range x = t) : IsTranscendenceBasis R ((↑) : t -> A)
参数：hx : IsTranscendenceBasis R x；ht : range x = t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTranscendenceBasis.to_subtype_range`：IsTranscendenceBasis.to_subtype_r
ange (hx : IsTranscendenceBasis R x) : IsTranscendenceBasis R ((↑) : range x -> 
A)
-/
theorem IsTranscendenceBasis.to_subtype_range' (hx : IsTranscendenceBasis R x) {t}
    (ht : range x = t) : IsTranscendenceBasis R ((↑) : t → A) :=
  ht ▸ hx.to_subtype_range
/-
**IsTranscendenceBasis.of_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.of_comp {x : ι -> A} (f : A ->ₐ[R] A') (h : Function.
Injective f) (H : IsTranscendenceBasis R (f ∘ x)) : IsTranscendenceBasis R x
参数：f : A ->ₐ[R] A'；h : Function.Injective f；H : IsTranscendenceBasis R (f ∘ x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgHom.algebraicIndependent_iff`：AlgHom.algebraicIndependent_iff (f : A 
->ₐ[R] A') (hf : Injective f) : AlgebraicIndependent R (f ∘ x) ↔ AlgebraicIndepe
ndent R x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `algebraicIndependent_image`：algebraicIndependent_image {ι} {s : Set ι} {
f : ι -> A} (hf : Set.InjOn f s) : (AlgebraicIndependent R fun x : s => f x) ↔ A
lgebraicIndepend…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Set.image_injective`：image_injective : Injective (image f) ↔ Injective f
-/
lemma IsTranscendenceBasis.of_comp {x : ι → A} (f : A →ₐ[R] A') (h : Function.Injective f)
    (H : IsTranscendenceBasis R (f ∘ x)) :
    IsTranscendenceBasis R x := by
  refine ⟨(AlgHom.algebraicIndependent_iff f h).mp H.1, ?_⟩
  intro s hs hs'
  have := H.2 (f '' s)
    ((algebraicIndependent_image h.injOn).mp ((AlgHom.algebraicIndependent_iff f h).mpr hs))
    (by rw [Set.range_comp]; exact Set.image_mono hs')
  rwa [Set.range_comp, (Set.image_injective.mpr h).eq_iff] at this
/-
**IsTranscendenceBasis.of_comp_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.of_comp_algebraMap [Algebra A A'] [IsScalarTower R A 
A'] [FaithfulSMul A A'] {x : ι -> A} (H : IsTranscendenceBasis R (algebraMap A A
' ∘ x)) : IsTranscendenceBasis R x
参数：H : IsTranscendenceBasis R (algebraMap A A' ∘ x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsTranscendenceBasis.of_comp`：IsTranscendenceBasis.of_comp {x : ι -> A} 
(f : A ->ₐ[R] A') (h : Function.Injective f) (H : IsTranscendenceBasis R (f ∘ x)
) : IsTranscendenc…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
lemma IsTranscendenceBasis.of_comp_algebraMap [Algebra A A'] [IsScalarTower R A A']
    [FaithfulSMul A A'] {x : ι → A} (H : IsTranscendenceBasis R (algebraMap A A' ∘ x)) :
    IsTranscendenceBasis R x :=
  .of_comp (IsScalarTower.toAlgHom R A A') (FaithfulSMul.algebraMap_injective A A') H

/-- Also see `IsTranscendenceBasis.algebraMap_comp`
for the composition with an algebraic extension. -/
/-
**AlgEquiv.isTranscendenceBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.isTranscendenceBasis (e : A ≃ₐ[R] A') (hx : IsTranscendenceBasis 
R x) : IsTranscendenceBasis R (e ∘ x)
参数：e : A ≃ₐ[R] A'；hx : IsTranscendenceBasis R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsTranscendenceBasis.of_comp`：IsTranscendenceBasis.of_comp {x : ι -> A} 
(f : A ->ₐ[R] A') (h : Function.Injective f) (H : IsTranscendenceBasis R (f ∘ x)
) : IsTranscendenc…
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Also see `IsTranscendenceBasis.algebraMap_comp`
for the composition with an algebraic extension.
-/
theorem AlgEquiv.isTranscendenceBasis (e : A ≃ₐ[R] A') (hx : IsTranscendenceBasis R x) :
    IsTranscendenceBasis R (e ∘ x) :=
  .of_comp e.symm.toAlgHom e.symm.injective (by convert! hx; ext; simp)
/-
**AlgEquiv.isTranscendenceBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.isTranscendenceBasis_iff (e : A ≃ₐ[R] A') : IsTranscendenceBasis 
R (e ∘ x) ↔ IsTranscendenceBasis R x
参数：e : A ≃ₐ[R] A'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgEquiv.isTranscendenceBasis`：AlgEquiv.isTranscendenceBasis (e : A ≃ₐ[R
] A') (hx : IsTranscendenceBasis R x) : IsTranscendenceBasis R (e ∘ x)
-/
theorem AlgEquiv.isTranscendenceBasis_iff (e : A ≃ₐ[R] A') :
    IsTranscendenceBasis R (e ∘ x) ↔ IsTranscendenceBasis R x :=
  ⟨fun hx ↦ by convert! e.symm.isTranscendenceBasis hx; ext; simp, e.isTranscendenceBasis⟩

section trdeg

open Cardinal

/-
**AlgebraicIndependent.lift_cardinalMk_le_trdeg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.lift_cardinalMk_le_trdeg [Nontrivial R] (hx : Algebra
icIndependent R x) : lift.{v} #ι <= lift.{u} (trdeg R A)
参数：hx : AlgebraicIndependent R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `AlgebraicIndependent.injective`：∀ {ι : Type u} {R : Type u_2} {A : Type 
v} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],
   AlgebraicIndepend…
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicIndependent.to_subtype_range`：AlgebraicIndependent.to_subtype_r
ange (hx : AlgebraicIndependent R x) : AlgebraicIndependent R ((↑) : range x -> 
A)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem AlgebraicIndependent.lift_cardinalMk_le_trdeg [Nontrivial R]
    (hx : AlgebraicIndependent R x) : lift.{v} #ι ≤ lift.{u} (trdeg R A) := by
  rw [lift_mk_eq'.mpr ⟨.ofInjective _ hx.injective⟩, lift_le]
  exact le_ciSup_of_le bddAbove_of_small ⟨_, hx.to_subtype_range⟩ le_rfl
/-
**AlgebraicIndependent.cardinalMk_le_trdeg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.cardinalMk_le_trdeg [Nontrivial R] {ι : Type v} {x : 
ι -> A} (hx : AlgebraicIndependent R x) : #ι <= trdeg R A
参数：hx : AlgebraicIndependent R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `AlgebraicIndependent.lift_cardinalMk_le_trdeg`：AlgebraicIndependent.lift
_cardinalMk_le_trdeg [Nontrivial R] (hx : AlgebraicIndependent R x) : lift.{v} #
ι <= lift.{u} (trdeg R A)
-/
theorem AlgebraicIndependent.cardinalMk_le_trdeg [Nontrivial R] {ι : Type v} {x : ι → A}
    (hx : AlgebraicIndependent R x) : #ι ≤ trdeg R A := by
  rw [← (#ι).lift_id, ← (trdeg R A).lift_id]; exact hx.lift_cardinalMk_le_trdeg
/-
**lift_trdeg_le_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_trdeg_le_of_injective (f : A ->ₐ[R] A') (hf : Injective f) : lift.{v'
} (trdeg R A) <= lift.{v} (trdeg R A')
参数：f : A ->ₐ[R] A'；hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trdeg_subsingleton`：∀ {R : Type u_2} {A : Type v} [inst : CommRing R] [i
nst_1 : CommRing A] [inst_2 : Algebra R A] [Subsingleton R],   Algebra.trdeg R A
 = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Algebra.trdeg.eq_1`：∀ (R : Type u_2) (A : Type v) [inst : CommRing R] [i
nst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.trdeg R A = ⨆ ι, Cardinal.
mk ↑↑ι
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `AlgebraicIndependent.lift_cardinalMk_le_trdeg`：AlgebraicIndependent.lift
_cardinalMk_le_trdeg [Nontrivial R] (hx : AlgebraicIndependent R x) : lift.{v} #
ι <= lift.{u} (trdeg R A)
· 使用定理 `AlgebraicIndependent.map'`：map' {f : A ->ₐ[R] A'} (hf_inj : Injective f)
 : AlgebraicIndependent R (f ∘ x)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem lift_trdeg_le_of_injective (f : A →ₐ[R] A') (hf : Injective f) :
    lift.{v'} (trdeg R A) ≤ lift.{v} (trdeg R A') := by
  nontriviality R
  rw [trdeg, lift_iSup bddAbove_of_small]
  exact ciSup_le' fun i ↦ (i.2.map' hf).lift_cardinalMk_le_trdeg
/-
**trdeg_le_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trdeg_le_of_injective {A' : Type v} [CommRing A'] [Algebra R A'] (f : A ->
ₐ[R] A') (hf : Injective f) : trdeg R A <= trdeg R A'
参数：f : A ->ₐ[R] A'；hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_trdeg_le_of_injective`：lift_trdeg_le_of_injective (f : A ->ₐ[R] A')
 (hf : Injective f) : lift.{v'} (trdeg R A) <= lift.{v} (trdeg R A')
-/
theorem trdeg_le_of_injective {A' : Type v} [CommRing A'] [Algebra R A'] (f : A →ₐ[R] A')
    (hf : Injective f) : trdeg R A ≤ trdeg R A' := by
  rw [← (trdeg R A).lift_id, ← (trdeg R A').lift_id]; exact lift_trdeg_le_of_injective f hf
/-
**lift_trdeg_le_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_trdeg_le_of_surjective (f : A ->ₐ[R] A') (hf : Surjective f) : lift.{
v} (trdeg R A') <= lift.{v'} (trdeg R A)
参数：f : A ->ₐ[R] A'；hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trdeg_subsingleton`：∀ {R : Type u_2} {A : Type v} [inst : CommRing R] [i
nst_1 : CommRing A] [inst_2 : Algebra R A] [Subsingleton R],   Algebra.trdeg R A
 = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Algebra.trdeg.eq_1`：∀ (R : Type u_2) (A : Type v) [inst : CommRing R] [i
nst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.trdeg R A = ⨆ ι, Cardinal.
mk ↑↑ι
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `AlgebraicIndependent.lift_cardinalMk_le_trdeg`：AlgebraicIndependent.lift
_cardinalMk_le_trdeg [Nontrivial R] (hx : AlgebraicIndependent R x) : lift.{v} #
ι <= lift.{u} (trdeg R A)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `AlgebraicIndependent.of_comp`：of_comp (f : A ->ₐ[R] A') (hfv : Algebraic
Independent R (f ∘ x)) : AlgebraicIndependent R x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.invFun_eq`：invFun_eq (h : exists a, f a = b) : f (invFun f b) =
 b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem lift_trdeg_le_of_surjective (f : A →ₐ[R] A') (hf : Surjective f) :
    lift.{v} (trdeg R A') ≤ lift.{v'} (trdeg R A) := by
  nontriviality R
  rw [trdeg, lift_iSup bddAbove_of_small]
  refine ciSup_le' fun i ↦ (lift_cardinalMk_le_trdeg (x := fun a : i.1 ↦ (⇑f).invFun a) <|
    of_comp f ?_)
  convert! i.2; simp [invFun_eq (hf _)]
/-
**trdeg_le_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trdeg_le_of_surjective {A' : Type v} [CommRing A'] [Algebra R A'] (f : A -
>ₐ[R] A') (hf : Surjective f) : trdeg R A' <= trdeg R A
参数：f : A ->ₐ[R] A'；hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_trdeg_le_of_surjective`：lift_trdeg_le_of_surjective (f : A ->ₐ[R] A
') (hf : Surjective f) : lift.{v} (trdeg R A') <= lift.{v'} (trdeg R A)
-/
theorem trdeg_le_of_surjective {A' : Type v} [CommRing A'] [Algebra R A'] (f : A →ₐ[R] A')
    (hf : Surjective f) : trdeg R A' ≤ trdeg R A := by
  rw [← (trdeg R A).lift_id, ← (trdeg R A').lift_id]; exact lift_trdeg_le_of_surjective f hf
/-
**AlgEquiv.lift_trdeg_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.lift_trdeg_eq (e : A ≃ₐ[R] A') : lift.{v'} (trdeg R A) = lift.{v}
 (trdeg R A')
参数：e : A ≃ₐ[R] A'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `lift_trdeg_le_of_injective`：lift_trdeg_le_of_injective (f : A ->ₐ[R] A')
 (hf : Injective f) : lift.{v'} (trdeg R A) <= lift.{v} (trdeg R A')
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `lift_trdeg_le_of_surjective`：lift_trdeg_le_of_surjective (f : A ->ₐ[R] A
') (hf : Surjective f) : lift.{v} (trdeg R A') <= lift.{v'} (trdeg R A)
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
-/
theorem AlgEquiv.lift_trdeg_eq (e : A ≃ₐ[R] A') :
    lift.{v'} (trdeg R A) = lift.{v} (trdeg R A') :=
  (lift_trdeg_le_of_injective e.toAlgHom e.injective).antisymm
    (lift_trdeg_le_of_surjective e.toAlgHom e.surjective)
/-
**AlgEquiv.trdeg_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.trdeg_eq {A' : Type v} [CommRing A'] [Algebra R A'] (e : A ≃ₐ[R] 
A') : trdeg R A = trdeg R A'
参数：e : A ≃ₐ[R] A'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `AlgEquiv.lift_trdeg_eq`：AlgEquiv.lift_trdeg_eq (e : A ≃ₐ[R] A') : lift.{
v'} (trdeg R A) = lift.{v} (trdeg R A')
-/
theorem AlgEquiv.trdeg_eq {A' : Type v} [CommRing A'] [Algebra R A'] (e : A ≃ₐ[R] A') :
    trdeg R A = trdeg R A' := by
  rw [← (trdeg R A).lift_id, e.lift_trdeg_eq, lift_id]

end trdeg

/-
**algebraicIndependent_comp_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_comp_subtype {s : Set ι} : AlgebraicIndependent R (x 
∘ (↑) : s -> A) ↔ forall p in MvPolynomial.supported R s, aeval x p = 0 -> p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `injective_iff_map_eq_zero'`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_
9} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [Add
MonoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `MvPolynomial.rename_injective`：rename_injective (f : σ -> τ) (hf : Funct
ion.Injective f) : Function.Injective (rename f : MvPolynomial σ R -> MvPolynomi
al τ R)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.supported_eq_range_rename`：supported_eq_range_rename (s : S
et σ) : supported R s = (rename ((↑) : s -> σ)).range
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem algebraicIndependent_comp_subtype {s : Set ι} :
    AlgebraicIndependent R (x ∘ (↑) : s → A) ↔
      ∀ p ∈ MvPolynomial.supported R s, aeval x p = 0 → p = 0 := by
  have : (aeval (x ∘ (↑) : s → A) : _ →ₐ[R] _) = (aeval x).comp (rename (↑)) := by ext; simp
  have : ∀ p : MvPolynomial s R, rename ((↑) : s → ι) p = 0 ↔ p = 0 :=
    (injective_iff_map_eq_zero' (rename ((↑) : s → ι) : MvPolynomial s R →ₐ[R] _).toRingHom).1
      (rename_injective _ Subtype.val_injective)
  simp [algebraicIndependent_iff, supported_eq_range_rename, *]
/-
**algebraicIndependent_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_subtype {s : Set A} : AlgebraicIndependent R ((↑) : s
 -> A) ↔ forall p : MvPolynomial A R, p in MvPolynomial.supported R s -> aeval i
d p = 0 -> p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraicIndependent_comp_subtype`：algebraicIndependent_comp_subtype {s 
: Set ι} : AlgebraicIndependent R (x ∘ (↑) : s -> A) ↔ forall p in MvPolynomial.
supported R s, aeval x …
-/
theorem algebraicIndependent_subtype {s : Set A} :
    AlgebraicIndependent R ((↑) : s → A) ↔
      ∀ p : MvPolynomial A R, p ∈ MvPolynomial.supported R s → aeval id p = 0 → p = 0 := by
  apply @algebraicIndependent_comp_subtype _ _ _ id
/-
**algebraicIndependent_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_of_finite (s : Set A) (H : forall t subseteq s, t.Fin
ite -> AlgebraicIndependent R ((↑) : t -> A)) : AlgebraicIndependent R ((↑) : s 
-> A)
参数：s : Set A；H : forall t subseteq s, t.Finite -> AlgebraicIndependent R ((↑) : 
t -> A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `algebraicIndependent_subtype`：algebraicIndependent_subtype {s : Set A} :
 AlgebraicIndependent R ((↑) : s -> A) ↔ forall p : MvPolynomial A R, p in MvPol
ynomial.supported …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.mem_supported`：mem_supported : p in supported R s ↔ ↑p.vars
 subseteq s
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem algebraicIndependent_of_finite (s : Set A)
    (H : ∀ t ⊆ s, t.Finite → AlgebraicIndependent R ((↑) : t → A)) :
    AlgebraicIndependent R ((↑) : s → A) :=
  algebraicIndependent_subtype.2 fun p hp ↦
    algebraicIndependent_subtype.1 (H _ (mem_supported.1 hp) (Finset.finite_toSet _)) _ (by simp)
/-
**algebraicIndependent_of_finite_type** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_of_finite_type (H : forall t : Set ι, t.Finite -> Alg
ebraicIndependent R fun i : t => x i) : AlgebraicIndependent R x
参数：H : forall t : Set ι, t.Finite -> AlgebraicIndependent R fun i : t => x i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `algebraicIndependent_comp_subtype`：algebraicIndependent_comp_subtype {s 
: Set ι} : AlgebraicIndependent R (x ∘ (↑) : s -> A) ↔ forall p in MvPolynomial.
supported R s, aeval x …
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `MvPolynomial.mem_supported_vars`：mem_supported_vars (p : MvPolynomial σ 
R) : p in supported R (↑p.vars : Set σ)
-/
theorem algebraicIndependent_of_finite_type
    (H : ∀ t : Set ι, t.Finite → AlgebraicIndependent R fun i : t ↦ x i) :
    AlgebraicIndependent R x :=
  (injective_iff_map_eq_zero _).mpr fun p ↦
    algebraicIndependent_comp_subtype.1 (H _ p.vars.finite_toSet) _ p.mem_supported_vars
/-
**AlgebraicIndependent.image_of_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.image_of_comp {ι ι'} (s : Set ι) (f : ι -> ι') (g : ι
' -> A) (hs : AlgebraicIndependent R fun x : s => g (f x)) : AlgebraicIndependen
t R fun x : f '' s => g x
参数：s : Set ι；f : ι -> ι'；g : ι' -> A；hs : AlgebraicIndependent R fun x : s => g 
(f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `AlgebraicIndependent.injective`：∀ {ι : Type u} {R : Type u_2} {A : Type 
v} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],
   AlgebraicIndepend…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `algebraicIndependent_equiv'`：algebraicIndependent_equiv' (e : ι ≃ ι') {f
 : ι' -> A} {g : ι -> A} (h : f ∘ e = g) : AlgebraicIndependent R g ↔ AlgebraicI
ndependent R f
-/
theorem AlgebraicIndependent.image_of_comp {ι ι'} (s : Set ι) (f : ι → ι') (g : ι' → A)
    (hs : AlgebraicIndependent R fun x : s => g (f x)) :
    AlgebraicIndependent R fun x : f '' s => g x := by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (algebraicIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs
/-
**AlgebraicIndependent.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.image {ι} {s : Set ι} {f : ι -> A} (hs : AlgebraicInd
ependent R fun x : s => f x) : AlgebraicIndependent R fun x : f '' s => (x : A)
参数：hs : AlgebraicIndependent R fun x : s => f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicIndependent.image_of_comp`：AlgebraicIndependent.image_of_comp {
ι ι'} (s : Set ι) (f : ι -> ι') (g : ι' -> A) (hs : AlgebraicIndependent R fun x
 : s => g (f x)) : Algeb…
-/
theorem AlgebraicIndependent.image {ι} {s : Set ι} {f : ι → A}
    (hs : AlgebraicIndependent R fun x : s => f x) :
    AlgebraicIndependent R fun x : f '' s => (x : A) := by
  convert! AlgebraicIndependent.image_of_comp s f id hs
/-
**algebraicIndependent_iUnion_of_directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_iUnion_of_directed {η : Type*} [Nonempty η] {s : η ->
 Set A} (hs : Directed (· subseteq ·) s) (h : forall i, AlgebraicIndependent R (
(↑) : s i -> A)) : AlgebraicIndependent R ((↑) : (⋃ i, s i) -> A)
参数：hs : Directed (· subseteq ·) s；h : forall i, AlgebraicIndependent R ((↑) : s 
i -> A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraicIndependent_of_finite`：algebraicIndependent_of_finite (s : Set 
A) (H : forall t subseteq s, t.Finite -> AlgebraicIndependent R ((↑) : t -> A)) 
: AlgebraicIndepende…
· 使用定理 `Set.finite_subset_iUnion`：finite_subset_iUnion {s : Set α} (hs : s.Finit
e) {ι} {t : ι -> Set α} (h : s subseteq ⋃ i, t i) : exists I : Set ι, I.Finite ∧
 s subseteq ⋃ …
· 使用定理 `Directed.finset_le`：Directed.finset_le {r : α -> α -> Prop} [IsTrans α r
] {ι} [hι : Nonempty ι] {f : ι -> α} (D : Directed r f) (s : Finset ι) : exists 
z, foral…
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `AlgebraicIndependent.mono`：mono {t s : Set A} (h : t subseteq s) (hx : A
lgebraicIndependent R ((↑) : s -> A)) : AlgebraicIndependent R ((↑) : t -> A)
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
-/
theorem algebraicIndependent_iUnion_of_directed {η : Type*} [Nonempty η] {s : η → Set A}
    (hs : Directed (· ⊆ ·) s) (h : ∀ i, AlgebraicIndependent R ((↑) : s i → A)) :
    AlgebraicIndependent R ((↑) : (⋃ i, s i) → A) := by
  refine algebraicIndependent_of_finite (⋃ i, s i) fun t ht ft => ?_
  rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
  rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
  exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
/-
**algebraicIndependent_sUnion_of_directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_sUnion_of_directed {s : Set (Set A)} (hsn : s.Nonempt
y) (hs : DirectedOn (· subseteq ·) s) (h : forall a in s, AlgebraicIndependent R
 ((↑) : a -> A)) : AlgebraicIndependent R ((↑) : ⋃₀ s -> A)
参数：Set A；hsn : s.Nonempty；hs : DirectedOn (· subseteq ·) s；h : forall a in s, Al
gebraicIndependent R ((↑) : a -> A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `algebraicIndependent_iUnion_of_directed`：algebraicIndependent_iUnion_of_
directed {η : Type*} [Nonempty η] {s : η -> Set A} (hs : Directed (· subseteq ·)
 s) (h : forall i, AlgebraicI…
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
-/
theorem algebraicIndependent_sUnion_of_directed {s : Set (Set A)} (hsn : s.Nonempty)
    (hs : DirectedOn (· ⊆ ·) s) (h : ∀ a ∈ s, AlgebraicIndependent R ((↑) : a → A)) :
    AlgebraicIndependent R ((↑) : ⋃₀ s → A) := by
  let : Nonempty s := Nonempty.to_subtype hsn
  rw [sUnion_eq_iUnion]
  exact algebraicIndependent_iUnion_of_directed hs.directed_val (by simpa using h)
/-
**exists_maximal_algebraicIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_maximal_algebraicIndependent (s t : Set A) (hst : s subseteq t) (hs
 : AlgebraicIndepOn R id s) : exists u, s subseteq u ∧ Maximal (fun (x : Set A) 
=> AlgebraicIndepOn R id x ∧ x subseteq t) u
参数：s t : Set A；hst : s subseteq t；hs : AlgebraicIndepOn R id s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_subset_nonempty`：zorn_subset_nonempty (S : Set (Set α)) (H : forall
 c subseteq S, IsChain (· subseteq ·) c -> c.Nonempty -> exists ub in S, forall 
s in c, s …
· 使用定理 `algebraicIndependent_sUnion_of_directed`：algebraicIndependent_sUnion_of_
directed {s : Set (Set A)} (hsn : s.Nonempty) (hs : DirectedOn (· subseteq ·) s)
 (h : forall a in s, Algebrai…
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
-/
theorem exists_maximal_algebraicIndependent (s t : Set A) (hst : s ⊆ t)
    (hs : AlgebraicIndepOn R id s) : ∃ u, s ⊆ u ∧
      Maximal (fun (x : Set A) ↦ AlgebraicIndepOn R id x ∧ x ⊆ t) u := by
  refine zorn_subset_nonempty { u : Set A | AlgebraicIndependent R ((↑) : u → A) ∧ u ⊆ t}
    (fun c hc chainc hcn ↦ ⟨⋃₀ c, ⟨?_, ?_⟩, fun _ ↦ subset_sUnion_of_mem⟩) s ⟨hs, hst⟩
  · exact algebraicIndependent_sUnion_of_directed hcn chainc.directedOn (fun x hxc ↦ (hc hxc).1)
  exact fun x ⟨w, hyc, hwy⟩ ↦ (hc hyc).2 hwy
/-
**AlgebraicIndependent.repr_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.repr_ker (hx : AlgebraicIndependent R x) : RingHom.ke
r (hx.repr : adjoin R (range x) ->+* MvPolynomial ι R) = ⊥
参数：hx : AlgebraicIndependent R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
theorem AlgebraicIndependent.repr_ker (hx : AlgebraicIndependent R x) :
    RingHom.ker (hx.repr : adjoin R (range x) →+* MvPolynomial ι R) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).1 (AlgEquiv.injective _)

-- TODO - make this an `AlgEquiv`
/-- The isomorphism between `MvPolynomial (Option ι) R` and the polynomial ring over
the algebra generated by an algebraically independent family. -/
/-
**AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin** 是 Mathlib 中的一个定
义，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin (hx : Algebra
icIndependent R x) : MvPolynomial (Option ι) R ≃+* Polynomial (adjoin R (Set.ran
ge x))
参数：hx : AlgebraicIndependent R x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `MvPolynomial (Option ι) R` and the polynomial ring over
the algebra generated by an algebraically independent family.
-/
def AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin (hx : AlgebraicIndependent R x) :
    MvPolynomial (Option ι) R ≃+* Polynomial (adjoin R (Set.range x)) :=
  (MvPolynomial.optionEquivLeft _ _).toRingEquiv.trans
    (Polynomial.mapEquiv hx.aevalEquiv.toRingEquiv)

@[simp]
/-
**AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply** 是 Mathlib
 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply (hx : A
lgebraicIndependent R x) (y) : hx.mvPolynomialOptionEquivPolynomialAdjoin y = Po
lynomial.map (hx.aevalEquiv : MvPolynomial ι R ->+* adjoin R (range x)) (aeval (
fun o : Option ι => o.elim Polynomial.X fun s : ι => Polynomial.C (X s)) y)
参数：hx : AlgebraicIndependent R x；y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply
    (hx : AlgebraicIndependent R x) (y) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin y =
      Polynomial.map (hx.aevalEquiv : MvPolynomial ι R →+* adjoin R (range x))
        (aeval (fun o : Option ι => o.elim Polynomial.X fun s : ι => Polynomial.C (X s)) y) :=
  rfl

/-- `simp`-normal form of `mvPolynomialOptionEquivPolynomialAdjoin_C` -/
@[simp]
/-
**AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C'** 是 Mathlib 中的
一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C' (hx : Alge
braicIndependent R x) (r) : Polynomial.C (hx.aevalEquiv (C r)) = Polynomial.C (a
lgebraMap _ _ r)
参数：hx : AlgebraicIndependent R x；r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicIndependent.aevalEquiv_apply_coe`：∀ {ι : Type u_1} {R : Type u_
3} {A : Type u_5} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A]   [inst_
2 : Algebra R A] (hx : Algebrai…
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`simp`-normal form of `mvPolynomialOptionEquivPolynomialAdjoin_C`
-/
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C'
    (hx : AlgebraicIndependent R x) (r) :
    Polynomial.C (hx.aevalEquiv (C r)) = Polynomial.C (algebraMap _ _ r) := by
  congr
  apply_fun Subtype.val using Subtype.val_injective
  simp
/-
**AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C (hx : Algeb
raicIndependent R x) (r) : hx.mvPolynomialOptionEquivPolynomialAdjoin (C r) = Po
lynomial.C (algebraMap _ _ r)
参数：hx : AlgebraicIndependent R x；r。
该定理/引理给出了一组等式。
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
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C'`：Algebra
icIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C' (hx : AlgebraicIndepend
ent R x) (r) : Polynomial.C (hx.aevalEquiv (C r)) = P…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C
    (hx : AlgebraicIndependent R x) (r) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin (C r) = Polynomial.C (algebraMap _ _ r) := by
  simp
/-
**AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_none** 是 Mathli
b 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_none (hx : 
AlgebraicIndependent R x) : hx.mvPolynomialOptionEquivPolynomialAdjoin (X none) 
= Polynomial.X
参数：hx : AlgebraicIndependent R x。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply`：Alge
braicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply (hx : AlgebraicIn
dependent R x) (y) : hx.mvPolynomialOptionEquivPolynomia…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Option.elim.eq_2`：∀ {α : Type u_1} {β : Sort u_2} (x : β) (x_1 : α → β),
 none.elim x x_1 = x
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
-/
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_none
    (hx : AlgebraicIndependent R x) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin (X none) = Polynomial.X := by
  rw [AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply, aeval_X, Option.elim,
    Polynomial.map_X]
/-
**AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_some** 是 Mathli
b 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_some (hx : 
AlgebraicIndependent R x) (i) : hx.mvPolynomialOptionEquivPolynomialAdjoin (X (s
ome i)) = Polynomial.C (hx.aevalEquiv (X i))
参数：hx : AlgebraicIndependent R x；i。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply`：Alge
braicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply (hx : AlgebraicIn
dependent R x) (y) : hx.mvPolynomialOptionEquivPolynomia…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Option.elim.eq_1`：∀ {α : Type u_1} {β : Sort u_2} (x : β) (x_1 : α → β) 
(x_3 : α), (some x_3).elim x x_1 = x_1 x_3
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
-/
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_some
    (hx : AlgebraicIndependent R x) (i) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin (X (some i)) =
      Polynomial.C (hx.aevalEquiv (X i)) := by
  rw [AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply, aeval_X, Option.elim,
    Polynomial.map_C, RingHom.coe_coe]
/-
**AlgebraicIndependent.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin** 是 Ma
thlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgebraicIndependent.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin (h
x : AlgebraicIndependent R x) (a : A) : RingHom.comp (↑(Polynomial.aeval a : Pol
ynomial (adjoin R (Set.range x)) ->ₐ[_] A) : Polynomial (adjoin R (Set.range x))
 ->+* A) hx.mvPolynomialOptionEquivPolynomialAdjoin.toRingHom = ↑(MvPolynomial.a
eval fun o : Option ι => o.elim a x : MvPolynomial (Option ι) R ->ₐ[R] A)
参数：hx : AlgebraicIndependent R x；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ringHom_ext`：ringHom_ext {A : Type*} [Semiring A] {f g : Mv
Polynomial σ R ->+* A} (hC : forall r, f (C r) = g (C r)) (hX : forall i, f (X i
) = g (X i)) :…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C`：Algebrai
cIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C (hx : AlgebraicIndependen
t R x) (r) : hx.mvPolynomialOptionEquivPolynomialAdj…
· 使用定理 `MvPolynomial.aeval_C`：aeval_C (r : R) : aeval f (C r) = algebraMap R S₁ 
r
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_none`：Alg
ebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_none (hx : Algebraic
Independent R x) : hx.mvPolynomialOptionEquivPolynomialAd…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Option.elim.eq_2`：∀ {α : Type u_1} {β : Sort u_2} (x : β) (x_1 : α → β),
 none.elim x x_1 = x
· 使用定理 `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_some`：Alg
ebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_some (hx : Algebraic
Independent R x) (i) : hx.mvPolynomialOptionEquivPolynomi…
· 使用定理 `AlgebraicIndependent.algebraMap_aevalEquiv`：algebraMap_aevalEquiv (p : M
vPolynomial ι R) : algebraMap (Algebra.adjoin R (range x)) A (hx.aevalEquiv p) =
 aeval x p
· 使用定理 `Option.elim.eq_1`：∀ {α : Type u_1} {β : Sort u_2} (x : β) (x_1 : α → β) 
(x_3 : α), (some x_3).elim x x_1 = x_1 x_3
-/
theorem AlgebraicIndependent.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin
    (hx : AlgebraicIndependent R x) (a : A) :
    RingHom.comp
        (↑(Polynomial.aeval a : Polynomial (adjoin R (Set.range x)) →ₐ[_] A) :
          Polynomial (adjoin R (Set.range x)) →+* A)
        hx.mvPolynomialOptionEquivPolynomialAdjoin.toRingHom =
      ↑(MvPolynomial.aeval fun o : Option ι => o.elim a x : MvPolynomial (Option ι) R →ₐ[R] A) := by
  refine MvPolynomial.ringHom_ext ?_ ?_ <;>
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgHom.coe_toRingHom, AlgHom.coe_toRingHom]
  · intro r
    rw [hx.mvPolynomialOptionEquivPolynomialAdjoin_C, aeval_C, Polynomial.aeval_C,
      IsScalarTower.algebraMap_apply R (adjoin R (range x)) A]
  · rintro (⟨⟩ | ⟨i⟩)
    · rw [hx.mvPolynomialOptionEquivPolynomialAdjoin_X_none, aeval_X, Polynomial.aeval_X,
        Option.elim]
    · rw [hx.mvPolynomialOptionEquivPolynomialAdjoin_X_some, Polynomial.aeval_C,
        hx.algebraMap_aevalEquiv, aeval_X, aeval_X, Option.elim]

section Field

variable {K : Type*} [Field K] [Algebra K A]

/-
**algebraicIndependent_empty_type** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_empty_type [IsEmpty ι] [Nontrivial A] : AlgebraicInde
pendent K x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraicIndependent_empty_type_iff`：algebraicIndependent_empty_type_iff
 [IsEmpty ι] : AlgebraicIndependent R x ↔ Injective (algebraMap R A)
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
-/
theorem algebraicIndependent_empty_type [IsEmpty ι] [Nontrivial A] : AlgebraicIndependent K x := by
  rw [algebraicIndependent_empty_type_iff]
  exact RingHom.injective _
/-
**algebraicIndependent_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicIndependent_empty [Nontrivial A] : AlgebraicIndependent K ((↑) : 
(∅ : Set A) -> A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraicIndependent_empty_type`：algebraicIndependent_empty_type [IsEmpt
y ι] [Nontrivial A] : AlgebraicIndependent K x
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
-/
theorem algebraicIndependent_empty [Nontrivial A] :
    AlgebraicIndependent K ((↑) : (∅ : Set A) → A) :=
  algebraicIndependent_empty_type

end Field

