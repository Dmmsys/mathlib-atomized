/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.Padics.WithVal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Topology.Algebra.Algebra.Equiv

/-!
# Isomorphisms between `adicCompletion ℚ` and `ℚ_[p]`

Let `R` have field of fractions `ℚ`. If `v : HeightOneSpectrum R`, then `v.adicCompletion ℚ` is
the uniform space completion of `ℚ` with respect to the `v`-adic valuation.
On the other hand, `ℚ_[p]` is the `p`-adic numbers, defined as the completion of `ℚ` with respect
to the `p`-adic norm using the completion of Cauchy sequences. This file constructs continuous
`ℚ`-algebra isomorphisms between the two, as well as continuous `ℤ`-algebra isomorphisms for their
respective rings of integers.

Isomorphisms are provided in both directions, allowing traversal of the following diagram:
```
HeightOneSpectrum R <----------->  Nat.Primes
          |                               |
          |                               |
          v                               v
v.adicCompletionIntegers ℚ  <------->   ℤ_[p]
          |                               |
          |                               |
          v                               v
v.adicCompletion ℚ  <--------------->   ℚ_[p]
```

## Main definitions
- `Rat.HeightOneSpectrum.primesEquiv` : the equivalence between height-one prime ideals of
  `R` and prime numbers in `ℕ`.
- `Rat.HeightOneSpectrum.padicEquiv v` : the continuous `ℚ`-algebra isomorphism
  `v.adicCompletion ℚ ≃A[ℚ] ℚ_[primesEquiv v]`.
- `Padic.adicCompletionEquiv p` : the continuous `ℚ`-algebra isomorphism
  `ℚ_[p] ≃A[ℚ] (primesEquiv.symm p).adicCompletion ℚ`.
- `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v` : the continuous `ℤ`-algebra
  isomorphism `v.adicCompletionIntegers ℚ ≃A[ℤ] ℤ_[natGenerator v]`.
- `PadicInt.adicCompletionIntegersEquiv p` : the continuous `ℤ`-algebra isomorphism
  `ℤ_[p] ≃A[ℤ] (primesEquiv.symm p).adicCompletionIntegers ℚ`.

TODO : Abstract the isomorphisms in this file using a universal predicate on adic completions,
along the lines of `IsComplete` + uniformity arises from a valuation + the valuations are
equivalent. It is best to do this after `Valued` has been refactored, or at least after
`adicCompletion` has `IsValuativeTopology` instance.
-/

@[expose] public section

open IsDedekindDomain UniformSpace.Completion NumberField PadicInt

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

variable (R : Type*) [CommRing R] [Algebra R ℚ]

/-
**Rat.int_algebraMap_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Rat.int_algebraMap_injective : Function.Injective (algebraMap Int R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `RingHom.injective_int`：RingHom.injective_int {α : Type*} [NonAssocRing α
] (f : Int ->+* α) [CharZero α] : Function.Injective f
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
-/
theorem Rat.int_algebraMap_injective : Function.Injective (algebraMap ℤ R) :=
  .of_comp (IsScalarTower.algebraMap_eq ℤ R ℚ ▸ RingHom.injective_int (algebraMap ℤ ℚ))

variable [IsIntegralClosure R ℤ ℚ]
/-
**Rat.int_algebraMap_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Rat.int_algebraMap_surjective [IsFractionRing R Rat] : Function.Surjective
 (algebraMap Int R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegrallyClosed.isIntegral_iff`：isIntegral_iff [IsIntegrallyClosed R]
 {x : K} : IsIntegral R x ↔ exists y : R, algebraMap R K y = x
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `IsIntegral.algebraMap`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra R 
A] [inst_4 …
· 使用定理 `IsIntegralClosure.isIntegral`：∀ (R : Type u_1) {A : Type u_2} (B : Type 
u_3) [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : CommRing B]   [inst_3 :
 Algebra R B] [ins…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Rat.int_algebraMap_surjective [IsFractionRing R ℚ] :
    Function.Surjective (algebraMap ℤ R) := by
  intro x
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 <|
    IsIntegral.algebraMap (B := ℚ) (IsIntegralClosure.isIntegral ℤ ℚ x)
  exact ⟨y, IsFractionRing.injective R ℚ <| by simp only [← IsScalarTower.algebraMap_apply, hy]⟩

/-- If `R` has field of fractions `ℚ` and is the integral closure of `ℤ` in `ℚ` then it is
isomorphic to `ℤ`. -/
/-
**Rat.IsIntegralClosure.intEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Rat.IsIntegralClosure.intEquiv : R ≃+* Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` has field of fractions `ℚ` and is the integral closure of `ℤ` in `ℚ` then
 it is
isomorphic to `ℤ`.
-/
noncomputable def Rat.IsIntegralClosure.intEquiv : R ≃+* ℤ :=
  (NumberField.RingOfIntegers.equiv R).symm.trans ringOfIntegersEquiv

@[simp]
/-
**Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv (x : 𝓞 Rat) : 
intEquiv (𝓞 Rat) x = ringOfIntegersEquiv x
参数：x : 𝓞 Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosureInt`：∀ {K : Type u_1} [i
nst : Field K], IsIntegralClosure (NumberField.RingOfIntegers K) ℤ K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIntegralClosure.isIntegral_algebra`：isIntegral_algebra [Algebra R A] [
IsScalarTower R A B] : Algebra.IsIntegral R A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsTorsionFree_2`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   Module.IsT
orsionFree (NumberField.RingOfIntege…
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
· 使用定理 `Classical.choose_eq`：∀ {α : Sort u_1} (a : α), ⋯.choose = a
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `RingHom.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocS
emiring α] [inst_1 : NonAssocSemiring β]   (toMonoidHom toMonoidHom_1 : α →* β) 
(e_toMonoid…
· 使用定理 `AlgHom.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R
 A] [inst_…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `AlgEquiv.map_mul'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `AlgEquiv.map_add'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `AlgEquiv.ofAlgHom.congr_simp`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `AlgEquiv.ofAlgHom_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂}
 [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3
 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv (x : 𝓞 ℚ) :
    intEquiv (𝓞 ℚ) x = ringOfIntegersEquiv x := by
  simp [intEquiv, RingOfIntegers.equiv, IsIntegralClosure.equiv, IsIntegralClosure.lift,
    IsIntegralClosure.mk']

namespace Rat.HeightOneSpectrum

variable {R : Type*} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]

/-- If `v : HeightOneSpectrum R` then `natGenerator v` is the generator in `ℕ` of the corresponding
ideal in `ℤ`. -/
/-
**Rat.HeightOneSpectrum.natGenerator** 是 Mathlib 中的一个定义，位于命名空间 `Rat.HeightOneSpe
ctrum`。
形式化陈述：natGenerator (v : HeightOneSpectrum R) : Nat
参数：v : HeightOneSpectrum R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `v : HeightOneSpectrum R` then `natGenerator v` is the generator in `ℕ` of th
e corresponding
ideal in `ℤ`.
-/
noncomputable def natGenerator (v : HeightOneSpectrum R) : ℕ :=
  Submodule.IsPrincipal.generator (v.asIdeal.map <| IsIntegralClosure.intEquiv R) |>.natAbs
/-
**Rat.HeightOneSpectrum.span_natGenerator** 是 Mathlib 中的一个定理，位于命名空间 `Rat.HeightO
neSpectrum`。
形式化陈述：span_natGenerator (v : HeightOneSpectrum R) : Ideal.span {(natGenerator v 
: Int)} = v.asIdeal.map (IsIntegralClosure.intEquiv R)
参数：v : HeightOneSpectrum R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Ideal.span_singleton_abs`：span_singleton_abs [LinearOrder α] : span {|x|
} = span {x}
· 使用定理 `Ideal.span_singleton_generator`：∀ {R : Type u} [inst : Semiring R] (I : 
Ideal R) [inst_1 : Submodule.IsPrincipal I],   Ideal.span {Submodule.IsPrincipal
.generator I} = I
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem span_natGenerator (v : HeightOneSpectrum R) :
    Ideal.span {(natGenerator v : ℤ)} = v.asIdeal.map (IsIntegralClosure.intEquiv R) := by
  simp [natGenerator]
/-
**Rat.HeightOneSpectrum.natGenerator_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat.Heig
htOneSpectrum`。
形式化陈述：natGenerator_dvd_iff (v : HeightOneSpectrum R) {n : Nat} : natGenerator v 
∣ n ↔ ↑n in v.asIdeal.map (IsIntegralClosure.intEquiv R)
参数：v : HeightOneSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.HeightOneSpectrum.span_natGenerator`：span_natGenerator (v : HeightOn
eSpectrum R) : Ideal.span {(natGenerator v : Int)} = v.asIdeal.map (IsIntegralCl
osure.intEquiv R)
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Int.ofNat_dvd`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
-/
theorem natGenerator_dvd_iff (v : HeightOneSpectrum R) {n : ℕ} :
    natGenerator v ∣ n ↔ ↑n ∈ v.asIdeal.map (IsIntegralClosure.intEquiv R) := by
  rw [← span_natGenerator, Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm
/-
**Rat.HeightOneSpectrum.prime_natGenerator** 是 Mathlib 中的一个定理，位于命名空间 `Rat.Height
OneSpectrum`。
形式化陈述：prime_natGenerator (v : HeightOneSpectrum R) : Nat.Prime (natGenerator v)
参数：v : HeightOneSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.prime_iff_natAbs_prime`：prime_iff_natAbs_prime {k : Int} : Prime k ↔
 Nat.Prime k.natAbs
· 使用定理 `Submodule.IsPrincipal.prime_generator_of_isPrime`：prime_generator_of_isP
rime (S : Ideal R) [S.IsPrincipal] [is_prime : S.IsPrime] (ne_bot : S != ⊥) : Pr
ime (generator S)
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.map_eq_bot_iff_of_injective`：map_eq_bot_iff_of_injective {I : Idea
l R} {f : F} (hf : Function.Injective f) : I.map f = ⊥ ↔ I = ⊥
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
-/
theorem prime_natGenerator (v : HeightOneSpectrum R) : Nat.Prime (natGenerator v) :=
  Int.prime_iff_natAbs_prime.1 <| Submodule.IsPrincipal.prime_generator_of_isPrime _
    ((Ideal.map_eq_bot_iff_of_injective (IsIntegralClosure.intEquiv R).injective).not.2 v.ne_bot)

variable [IsDedekindDomain R] [IsFractionRing R ℚ]

/-- The equivalence between height-one prime ideals of `R` and primes in `ℕ`. -/
/-
**Rat.HeightOneSpectrum.primesEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Rat.HeightOneSpec
trum`。
形式化陈述：primesEquiv : HeightOneSpectrum R ≃ Nat.Primes where toFun v
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.HeightOneSpectrum.prime_natGenerator`：prime_natGenerator (v : Height
OneSpectrum R) : Nat.Prime (natGenerator v)

--- 原说明 ---
The equivalence between height-one prime ideals of `R` and primes in `ℕ`.
-/
noncomputable def primesEquiv : HeightOneSpectrum R ≃ Nat.Primes where
  toFun v := ⟨natGenerator v, prime_natGenerator v⟩
  invFun p :=
    have h : Prime ((Ideal.span {(p.1 : ℤ)}).map (IsIntegralClosure.intEquiv R).symm) :=
      Ideal.map_prime_of_equiv _ (by simp [← Nat.prime_iff_prime_int, p.2]) (by simp [p.2.ne_zero])
    .ofPrime h
  left_inv v := by
    simp only [Ideal.map_symm]
    congr
    rw [← v.asIdeal.comap_map_of_bijective _ (IsIntegralClosure.intEquiv R).bijective,
      ← span_natGenerator]
  right_inv p := by
    simp only [Ideal.map_symm, natGenerator, HeightOneSpectrum.ofPrime_asIdeal]
    congr
    simp [Ideal.map_comap_of_surjective _ (IsIntegralClosure.intEquiv R).surjective,
      Int.associated_iff_natAbs.1 (Submodule.IsPrincipal.associated_generator_span_self _)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Rat.HeightOneSpectrum.valuation_equiv_padicValuation** 是 Mathlib 中的一个定理，位于命名空间
 `Rat.HeightOneSpectrum`。
形式化陈述：valuation_equiv_padicValuation (v : HeightOneSpectrum R) : (v.valuation Ra
t).IsEquiv (padicValuation (primesEquiv v))
参数：v : HeightOneSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `instFactPrimeValNat`：∀ (p : Nat.Primes), Fact (Nat.Prime ↑p)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.HeightOneSpectrum.prime_natGenerator`：prime_natGenerator (v : Height
OneSpectrum R) : Nat.Prime (natGenerator v)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Ideal.map_symm`：map_symm {I : Ideal S} (f : R ≃+* S) : I.map f.symm = I.
comap f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ofPrime.congr_simp`：∀ {R : Type u_1} 
[inst : CommRing R] [inst_1 : IsDedekindDomain R] {p p_1 : Ideal R} (e_p : p = p
_1) (hp : Prime p),   IsDedekindDomain.Heig…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `Rat.padicValuation.congr_simp`：∀ (p p_1 : ℕ) (e_p : p = p_1) [inst : Fac
t (Nat.Prime p)], Rat.padicValuation p = Rat.padicValuation p_1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.apply_mem_of_equiv_iff`：apply_mem_of_equiv_iff {I : Ideal R} {f : 
R ≃+* S} {x : R} : f x in I.map f ↔ x in I
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem valuation_equiv_padicValuation (v : HeightOneSpectrum R) :
    (v.valuation ℚ).IsEquiv (padicValuation (primesEquiv v)) := by
  simp [primesEquiv, Valuation.isEquiv_iff_val_le_one, valuation_le_one_iff_den,
    padicValuation_le_one_iff, natGenerator_dvd_iff,
    map_natCast (IsIntegralClosure.intEquiv R) _ ▸ Ideal.apply_mem_of_equiv_iff]

open Valuation

/-- The uniform space isomorphism `ℚ ≃ᵤ ℚ`, where the LHS has the uniformity from
`HeightOneSpectrum.valuation ℚ v` and the RHS has uniformity from
`Rat.padicValuation (natGenerator v)`, for a height-one prime ideal
`v : HeightOneSpectrum R`. -/
/-
**Rat.HeightOneSpectrum.withValEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Rat.HeightOneSpe
ctrum`。
形式化陈述：withValEquiv (v : HeightOneSpectrum R) : WithVal (v.valuation Rat) ≃ᵤ With
Val (padicValuation (primesEquiv v))
参数：v : HeightOneSpectrum R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.HeightOneSpectrum.valuation_equiv_padicValuation`：valuation_equiv_pa
dicValuation (v : HeightOneSpectrum R) : (v.valuation Rat).IsEquiv (padicValuati
on (primesEquiv v))

--- 原说明 ---
The uniform space isomorphism `ℚ ≃ᵤ ℚ`, where the LHS has the uniformity from
`HeightOneSpectrum.valuation ℚ v` and the RHS has uniformity from
`Rat.padicValuation (natGenerator v)`, for a height-one prime ideal
`v : HeightOneSpectrum R`.
-/
noncomputable def withValEquiv (v : HeightOneSpectrum R) :
    WithVal (v.valuation ℚ) ≃ᵤ WithVal (padicValuation (primesEquiv v)) :=
  (valuation_equiv_padicValuation v).uniformEquiv

/-- The continuous `ℚ`-algebra isomorphism between `v.adicCompletion ℚ` and `ℚ_[primesEquiv v]`. -/
/-
**Rat.HeightOneSpectrum.adicCompletion.padicEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Rat
.HeightOneSpectrum.adicCompletion`。
形式化陈述：{R : Type u_2} →   [inst : CommRing R] →     [inst_1 : Algebra R ℚ] →     
  [inst_2 : IsIntegralClosure R ℤ ℚ] →         [inst_3 : IsDedekindDomain R] →  
         [inst_4 : IsFractionRing R ℚ] →             (v : IsDedekindDomain.Heigh
tOneSpectrum R) →               IsDedekindDomain.HeightOneSpectrum.adicCompletio
n ℚ v ≃A[ℚ] ℚ_[↑(Rat.HeightOneSpectrum.primesEquiv v)]
参数：v : IsDedekindDomain.HeightOneSpectrum R；Rat.HeightOneSpectrum.primesEquiv v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous `ℚ`-algebra isomorphism between `v.adicCompletion ℚ` and `ℚ_[prim
esEquiv v]`.
-/
noncomputable def adicCompletion.padicEquiv (v : HeightOneSpectrum R) :
    v.adicCompletion ℚ ≃A[ℚ] ℚ_[primesEquiv v] where
  __ := (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv ℚ v).trans <|
    (mapRingEquiv _ (withValEquiv v).continuous
      (withValEquiv v).symm.continuous).trans Padic.withValRingEquiv
  __ := ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv ℚ v).trans <|
    (mapEquiv (withValEquiv v)).trans Padic.withValUniformEquiv).toHomeomorph
  commutes' := by simp

/-- The continuous `ℤ`-algebra isomorphism between `v.adicCompletionIntegers ℚ` and
`ℤ_[primesEquiv v]`. -/
/-
**Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv** 是 Mathlib 中的一个定义，
位于命名空间 `Rat.HeightOneSpectrum.adicCompletionIntegers`。
形式化陈述：{R : Type u_2} →   [inst : CommRing R] →     [inst_1 : Algebra R ℚ] →     
  [inst_2 : IsIntegralClosure R ℤ ℚ] →         [inst_3 : IsDedekindDomain R] →  
         [inst_4 : IsFractionRing R ℚ] →             (v : IsDedekindDomain.Heigh
tOneSpectrum R) →               ↥(IsDedekindDomain.HeightOneSpectrum.adicComplet
ionIntegers ℚ v) ≃A[ℤ]                 ℤ_[↑(Rat.HeightOneSpectrum.primesEquiv v)
]
参数：v : IsDedekindDomain.HeightOneSpectrum R；IsDedekindDomain.HeightOneSpectrum.a
dicCompletionIntegers ℚ v；Rat.HeightOneSpectrum.primesEquiv v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous `ℤ`-algebra isomorphism between `v.adicCompletionIntegers ℚ` and
`ℤ_[primesEquiv v]`.
-/
noncomputable def adicCompletionIntegers.padicIntEquiv (v : HeightOneSpectrum R) :
    v.adicCompletionIntegers ℚ ≃A[ℤ] ℤ_[primesEquiv v] where
  __ := let e0 := (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv ℚ v).restrict
          (v.adicCompletionIntegers ℚ)
          (Valued.v (R := (v.valuation ℚ).Completion)).valuationSubring
          fun _ ↦ by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; rfl
        let e := (mapRingEquiv _ (withValEquiv v).continuous
          (withValEquiv v).symm.continuous).restrict _ _ fun _ ↦ by
            simpa using! (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
        (e0.trans e).trans withValIntegersRingEquiv
  __ := let e0 := (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv ℚ v).subtype
          fun _ ↦ by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; rfl
        let e := (mapEquiv (withValEquiv v)).subtype fun _ ↦ by
          simpa using! (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
        ((e0.trans e).trans withValIntegersUniformEquiv).toHomeomorph
  commutes' := by simp

/-- The diagram
```
v.adicCompletionIntegers ℚ  ----->  ℤ_[primesEquiv v]
      |                               |
      |                               |
      v                               v
v.adicCompletion ℚ  ------------->  ℚ_[primesEquiv v]
```
commutes. -/
/-
**Rat.HeightOneSpectrum.adicCompletionIntegers.coe_padicIntEquiv_apply** 是 Mathl
ib 中的一个定理，位于命名空间 `Rat.HeightOneSpectrum.adicCompletionIntegers`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] [inst_1 : Algebra R ℚ] [inst_2 : IsIn
tegralClosure R ℤ ℚ]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFractionRing R 
ℚ] (v : IsDedekindDomain.HeightOneSpectrum R)   (x : ↥(IsDedekindDomain.HeightOn
eSpectrum.adicCompletionIntegers ℚ v)),   ↑((Rat.HeightOneSpectrum.adicCompletio
nIntegers.padicIntEquiv v) x) =     (Rat.HeightOneSpectrum.adicCompletion.padicE
quiv v) ↑x
参数：v : IsDedekindDomain.HeightOneSpectrum R；x : ↥(IsDedekindDomain.HeightOneSpec
trum.adicCompletionIntegers ℚ v)；(Rat.HeightOneSpectrum.adicCompletionIntegers.p
adicIntEquiv v) x；Rat.HeightOneSpectrum.adicCompletion.padicEquiv v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFactPrimeValNat`：∀ (p : Nat.Primes), Fact (Nat.Prime ↑p)
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K

--- 原说明 ---
The diagram
```
v.adicCompletionIntegers ℚ  ----->  ℤ_[primesEquiv v]
      |                               |
      |                               |
      v                               v
v.adicCompletion ℚ  ------------->  ℚ_[primesEquiv v]
```
commutes.
-/
theorem adicCompletionIntegers.coe_padicIntEquiv_apply (v : HeightOneSpectrum R)
    (x : v.adicCompletionIntegers ℚ) : padicIntEquiv v x = adicCompletion.padicEquiv v x := rfl

/-- The diagram
```
v.adicCompletionIntegers ℚ  <-----  ℤ_[primesEquiv v]
      |                               |
      |                               |
      v                               v
v.adicCompletion ℚ  <-------------  ℚ_[primesEquiv v]
```
commutes. -/
/-
**Rat.HeightOneSpectrum.adicCompletionIntegers.coe_padicIntEquiv_symm_apply** 是 
Mathlib 中的一个定理，位于命名空间 `Rat.HeightOneSpectrum.adicCompletionIntegers`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] [inst_1 : Algebra R ℚ] [inst_2 : IsIn
tegralClosure R ℤ ℚ]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFractionRing R 
ℚ] (v : IsDedekindDomain.HeightOneSpectrum R)   (x : ℤ_[↑(Rat.HeightOneSpectrum.
primesEquiv v)]),   ↑((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEqui
v v).symm x) =     (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm ↑x
参数：v : IsDedekindDomain.HeightOneSpectrum R；x : ℤ_[↑(Rat.HeightOneSpectrum.prime
sEquiv v)]；(Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm x
；Rat.HeightOneSpectrum.adicCompletion.padicEquiv v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFactPrimeValNat`：∀ (p : Nat.Primes), Fact (Nat.Prime ↑p)
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K

--- 原说明 ---
The diagram
```
v.adicCompletionIntegers ℚ  <-----  ℤ_[primesEquiv v]
      |                               |
      |                               |
      v                               v
v.adicCompletion ℚ  <-------------  ℚ_[primesEquiv v]
```
commutes.
-/
theorem adicCompletionIntegers.coe_padicIntEquiv_symm_apply (v : HeightOneSpectrum R)
    (x : ℤ_[primesEquiv v]) : (adicCompletionIntegers.padicIntEquiv v).symm x =
      (adicCompletion.padicEquiv v).symm x := rfl
/-
**Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn** 是 Mathlib 中的一个定理，位于命名空
间 `Rat.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] [inst_1 : Algebra R ℚ] [inst_2 : IsIn
tegralClosure R ℤ ℚ]   [inst_3 : IsDedekindDomain R] [inst_4 : IsFractionRing R 
ℚ] (v : IsDedekindDomain.HeightOneSpectrum R),   Set.BijOn ⇑(Rat.HeightOneSpectr
um.adicCompletion.padicEquiv v)     ↑(IsDedekindDomain.HeightOneSpectrum.adicCom
pletionIntegers ℚ v)     ↑(PadicInt.subring ↑(Rat.HeightOneSpectrum.primesEquiv 
v))
参数：v : IsDedekindDomain.HeightOneSpectrum R；Rat.HeightOneSpectrum.adicCompletion
.padicEquiv v；IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v；Padi
cInt.subring ↑(Rat.HeightOneSpectrum.primesEquiv v)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFactPrimeValNat`：∀ (p : Nat.Primes), Fact (Nat.Prime ↑p)
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.HeightOneSpectrum.adicCompletionIntegers.coe_padicIntEquiv_apply`：∀ 
{R : Type u_2} [inst : CommRing R] [inst_1 : Algebra R ℚ] [inst_2 : IsIntegralCl
osure R ℤ ℚ]   [inst_3 : IsDedekindDomain R] [inst_4 : IsF…
· 使用定理 `PadicInt.norm_le_one`：norm_le_one (z : Int_[p]) : ‖z‖ <= 1
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `ContinuousAlgEquiv.surjective`：surjective (e : A ≃A[R] B) : Function.Sur
jective e
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem adicCompletion.padicEquiv_bijOn (v : HeightOneSpectrum R) :
    Set.BijOn (padicEquiv v) (v.adicCompletionIntegers ℚ) (subring (primesEquiv v)) := by
  refine ⟨fun x hx ↦ ?_, (padicEquiv v).injective.injOn, fun y hy ↦ ?_⟩
  · rw [← adicCompletionIntegers.coe_padicIntEquiv_apply v ⟨x, hx⟩]
    exact norm_le_one ((adicCompletionIntegers.padicIntEquiv v) ⟨x, hx⟩)
  · obtain ⟨x, hx⟩ := (adicCompletionIntegers.padicIntEquiv v).surjective ⟨y, hy⟩
    refine ⟨x, x.2, by rw [← adicCompletionIntegers.coe_padicIntEquiv_apply, hx]⟩

end Rat.HeightOneSpectrum

open Rat.HeightOneSpectrum

namespace Padic

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]
  [IsIntegralClosure R ℤ ℚ]

/-- The continuous `ℚ`-algebra isomorphism between `ℚ_[p]` and
`(primesEquiv.symm p).adicCompletion ℚ`. -/
/-
**Padic.adicCompletionEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Padic`。
形式化陈述：adicCompletionEquiv (p : Nat.Primes) : Rat_[p] ≃A[Rat] ((primesEquiv (R
参数：p : Nat.Primes。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instFactPrimeValNat`：∀ (p : Nat.Primes), Fact (Nat.Prime ↑p)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The continuous `ℚ`-algebra isomorphism between `ℚ_[p]` and
`(primesEquiv.symm p).adicCompletion ℚ`.
-/
noncomputable def adicCompletionEquiv (p : Nat.Primes) :
    ℚ_[p] ≃A[ℚ] ((primesEquiv (R := R)).symm p).adicCompletion ℚ := by
  apply (ContinuousAlgEquiv.cast (primesEquiv.apply_symm_apply p).symm).trans
    (adicCompletion.padicEquiv (primesEquiv.symm p)).symm

end Padic

namespace PadicInt

open Padic

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]
  [IsIntegralClosure R ℤ ℚ]

/-- The continuous `ℤ`-algebra isomorphism between `ℤ_[p]` and
`(primesEquiv.symm p).adicCompletionIntegers ℚ`. -/
/-
**PadicInt.adicCompletionIntegersEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：adicCompletionIntegersEquiv (p : Nat.Primes) : Int_[p] ≃A[Int] ((primesEqu
iv (R
参数：p : Nat.Primes。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instFactPrimeValNat`：∀ (p : Nat.Primes), Fact (Nat.Prime ↑p)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The continuous `ℤ`-algebra isomorphism between `ℤ_[p]` and
`(primesEquiv.symm p).adicCompletionIntegers ℚ`.
-/
noncomputable def adicCompletionIntegersEquiv (p : Nat.Primes) :
    ℤ_[p] ≃A[ℤ] ((primesEquiv (R := R)).symm p).adicCompletionIntegers ℚ := by
  apply (ContinuousAlgEquiv.cast (primesEquiv.apply_symm_apply p).symm).trans
    (adicCompletionIntegers.padicIntEquiv (primesEquiv.symm p)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The diagram
```
ℤ_[p]  -------->  (primesEquiv.symm p).adicCompletionIntegers ℚ
   |                          |
   |                          |
   v                          v
ℚ_[p]  -------->  (primesEquiv.symm p).adicCompletion ℚ
```
commutes. -/
/-
**PadicInt.coe_adicCompletionIntegersEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Padi
cInt`。
形式化陈述：coe_adicCompletionIntegersEquiv_apply (p : Nat.Primes) (x : Int_[p]) : (ad
icCompletionIntegersEquiv R p x) = adicCompletionEquiv R p x
参数：p : Nat.Primes；x : Int_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFactPrimeValNat`：∀ (p : Nat.Primes), Fact (Nat.Prime ↑p)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subtype.heq_iff_coe_heq`：heq_iff_coe_heq {α β : Sort _} {p : α -> Prop} 
{q : β -> Prop} {a : {x // p x}} {b : {y // q y}} (h : α = β) (h' : p ≍ q) : a ≍
 b ↔ (a : α) …
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `cast_heq`：∀ {α β : Sort u} (h : α = β) (a : α), cast h a ≍ a

--- 原说明 ---
The diagram
```
ℤ_[p]  -------->  (primesEquiv.symm p).adicCompletionIntegers ℚ
   |                          |
   |                          |
   v                          v
ℚ_[p]  -------->  (primesEquiv.symm p).adicCompletion ℚ
```
commutes.
-/
theorem coe_adicCompletionIntegersEquiv_apply (p : Nat.Primes) (x : ℤ_[p]) :
    (adicCompletionIntegersEquiv R p x) = adicCompletionEquiv R p x := by
  simp only [adicCompletionIntegersEquiv, ContinuousAlgEquiv.trans_apply,
    adicCompletionIntegers.coe_padicIntEquiv_symm_apply,
    adicCompletionEquiv, ContinuousAlgEquiv.trans_apply, ContinuousAlgEquiv.cast_apply,
    EmbeddingLike.apply_eq_iff_eq, Equiv.cast_apply, eq_cast_iff_heq]
  rw [← Subtype.heq_iff_coe_heq (by rw [primesEquiv.apply_symm_apply])
    (by rw [primesEquiv.apply_symm_apply])]
  exact cast_heq _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- The diagram
```
ℤ_[p]  <--------  (primesEquiv.symm p).adicCompletionIntegers ℚ
   |                          |
   |                          |
   v                          v
ℚ_[p]  <--------  (primesEquiv.symm p).adicCompletion ℚ
```
commutes. -/
/-
**PadicInt.coe_adicCompletionIntegersEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 
`PadicInt`。
形式化陈述：coe_adicCompletionIntegersEquiv_symm_apply (p : Nat.Primes) (x : (primesEq
uiv.symm p).adicCompletionIntegers Rat) : (adicCompletionIntegersEquiv R p).symm
 x = (adicCompletionEquiv R p).symm x
参数：p : Nat.Primes；x : (primesEquiv.symm p).adicCompletionIntegers Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instFactPrimeValNat`：∀ (p : Nat.Primes), Fact (Nat.Prime ↑p)
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousAlgEquiv.symm_trans_apply`：symm_trans_apply (e₁ : B ≃A[R] A) (
e₂ : C ≃A[R] B) (a : A) : (e₂.trans e₁).symm a = e₂.symm (e₁.symm a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousAlgEquiv.symm_symm`：symm_symm (e : A ≃A[R] B) : e.symm.symm = 
e
· 使用定理 `ContinuousAlgEquiv.cast_symm_apply`：cast_symm_apply {ι : Type*} {A : ι -
> Type*} [(i : ι) -> Semiring (A i)] [(i : ι) -> Algebra R (A i)] [(i : ι) -> To
pologicalSpace (A i)] {i…
· 使用定理 `Equiv.cast_apply`：∀ {α β : Sort u_1} (h : α = β) (x : α), (Equiv.cast h)
 x = cast h x
· 使用引理 `Subtype.heq_iff_coe_heq`：heq_iff_coe_heq {α β : Sort _} {p : α -> Prop} 
{q : β -> Prop} {a : {x // p x}} {b : {y // q y}} (h : α = β) (h' : p ≍ q) : a ≍
 b ↔ (a : α) …
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `cast_heq`：∀ {α β : Sort u} (h : α = β) (a : α), cast h a ≍ a

--- 原说明 ---
The diagram
```
ℤ_[p]  <--------  (primesEquiv.symm p).adicCompletionIntegers ℚ
   |                          |
   |                          |
   v                          v
ℚ_[p]  <--------  (primesEquiv.symm p).adicCompletion ℚ
```
commutes.
-/
theorem coe_adicCompletionIntegersEquiv_symm_apply (p : Nat.Primes)
    (x : (primesEquiv.symm p).adicCompletionIntegers ℚ) :
    (adicCompletionIntegersEquiv R p).symm x = (adicCompletionEquiv R p).symm x := by
  simp -implicitDefEqProofs only [adicCompletionIntegersEquiv, ContinuousAlgEquiv.symm_trans_apply,
    ContinuousAlgEquiv.symm_symm, adicCompletionEquiv, Equiv.cast_apply, eq_cast_iff_heq,
    ← adicCompletionIntegers.coe_padicIntEquiv_apply, ContinuousAlgEquiv.cast_symm_apply]
  rw [← Subtype.heq_iff_coe_heq (by rw [primesEquiv.apply_symm_apply])
    (by rw [primesEquiv.apply_symm_apply])]
  exact cast_heq _ _

end PadicInt

