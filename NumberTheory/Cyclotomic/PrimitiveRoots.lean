/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Riccardo Brasca, Eric Rodriguez
-/
module

public import Mathlib.Data.Nat.Factorization.LCM
public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.Data.PNat.Prime
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Primitive roots in cyclotomic fields

If `IsCyclotomicExtension {n} A B`, we define an element `zeta n A B : B` that is a primitive
`n`th-root of unity in `B` and we study its properties. We also prove related theorems under the
more general assumption of just being a primitive root, for reasons described in the implementation
details section.

## Main definitions
* `IsCyclotomicExtension.zeta n A B`: if `IsCyclotomicExtension {n} A B`, then `zeta n A B`
  is a primitive `n`-th root of unity in `B`.
* `IsPrimitiveRoot.powerBasis`: if `K` and `L` are fields such that
  `IsCyclotomicExtension {n} K L`, then `IsPrimitiveRoot.powerBasis`
  gives a `K`-power basis for `L` given a primitive root `ζ`.
* `IsPrimitiveRoot.embeddingsEquivPrimitiveRoots`: the equivalence between `L →ₐ[K] A`
  and `primitiveRoots n A` given by the choice of `ζ`.

## Main results
* `IsCyclotomicExtension.zeta_spec`: `zeta n A B` is a primitive `n`-th root of unity.
* `IsCyclotomicExtension.finrank`: if `Irreducible (cyclotomic n K)` (in particular for
  `K = ℚ`), then the `finrank` of a cyclotomic extension is `n.totient`.
* `IsPrimitiveRoot.norm_eq_one`: if `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`),
  the norm of a primitive root is `1` if `n ≠ 2`.
* `IsPrimitiveRoot.sub_one_norm_eq_eval_cyclotomic`: if `Irreducible (cyclotomic n K)`
  (in particular for `K = ℚ`), then the norm of `ζ - 1` is `eval 1 (cyclotomic n ℤ)`, for a
  primitive root `ζ`. We also prove the analogous of this result for `zeta`.
* `IsPrimitiveRoot.norm_pow_sub_one_of_prime_pow_ne_two` : if
  `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
  then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` `p ^ (k - s + 1) ≠ 2`. See the following
  lemmas for similar results. We also prove the analogous of this result for `zeta`.
* `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two` : if `Irreducible (cyclotomic (p ^ (k + 1)) K)`
  (in particular for `K = ℚ`) and `p` is an odd prime, then the norm of `ζ - 1` is `p`. We also
  prove the analogous of this result for `zeta`.
* `IsPrimitiveRoot.embeddingsEquivPrimitiveRoots`: the equivalence between `L →ₐ[K] A`
  and `primitiveRoots n A` given by the choice of `ζ`.

## Implementation details
`zeta n A B` is defined as any primitive root of unity in `B`, - this must exist, by definition of
`IsCyclotomicExtension`. It is not true in general that it is a root of `cyclotomic n B`,
but this holds if `isDomain B` and `NeZero (n : B)`.

`zeta n A B` is defined using `Exists.choose`, which means we cannot control it.
For example, in normal mathematics, we can demand that `(zeta p ℤ ℤ[ζₚ] : ℚ(ζₚ))` is equal to
`zeta p ℚ ℚ(ζₚ)`, as we are just choosing "an arbitrary primitive root" and we can internally
specify that our choices agree. This is not the case here, and it is indeed impossible to prove that
these two are equal. Therefore, whenever possible, we prove our results for any primitive root,
and only at the "final step", when we need to provide an "explicit" primitive root, we use `zeta`.

-/

@[expose] public section


open Polynomial Algebra Finset Module IsCyclotomicExtension Nat PNat Set
open scoped IntermediateField

universe u v w z

variable {p n : ℕ} [NeZero n] (A : Type w) (B : Type z) (K : Type u) {L : Type v} (C : Type w)
variable [CommRing A] [CommRing B] [Algebra A B] [IsCyclotomicExtension {n} A B]

section Zeta

namespace IsCyclotomicExtension

variable (n)

/-- If `B` is an `n`-th cyclotomic extension of `A`, then `zeta n A B` is a primitive root of
unity in `B`. -/
/-
**IsCyclotomicExtension.zeta** 是 Mathlib 中的一个定义，位于命名空间 `IsCyclotomicExtension`。
形式化陈述：zeta : B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `B` is an `n`-th cyclotomic extension of `A`, then `zeta n A B` is a primitiv
e root of
unity in `B`.
-/
noncomputable def zeta : B :=
  (exists_isPrimitiveRoot A B (Set.mem_singleton n) (NeZero.ne _) :
    ∃ r : B, IsPrimitiveRoot r n).choose

/-- `zeta n A B` is a primitive `n`-th root of unity. -/
@[simp]
/-
**IsCyclotomicExtension.zeta_spec** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomicExtensi
on`。
形式化陈述：zeta_spec : IsPrimitiveRoot (zeta n A B) n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `IsCyclotomicExtension.exists_isPrimitiveRoot`：∀ {S : Set ℕ} (A : Type u)
 (B : Type v) {inst : CommRing A} {inst_1 : CommRing B} {inst_2 : Algebra A B}  
 [self : IsCyclotomicExtension S A…
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0

--- 原说明 ---
`zeta n A B` is a primitive `n`-th root of unity.
-/
theorem zeta_spec : IsPrimitiveRoot (zeta n A B) n :=
  (exists_isPrimitiveRoot A B (Set.mem_singleton n) (NeZero.ne _) :
    ∃ r : B, IsPrimitiveRoot r n).choose_spec
/-
**IsCyclotomicExtension.aeval_zeta** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomicExtens
ion`。
形式化陈述：aeval_zeta [IsDomain B] [NeZero (n : B)] : aeval (zeta n A B) (cyclotomic 
n A) = 0
参数：n : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `Polynomial.map_cyclotomic`：map_cyclotomic (n : Nat) {R S : Type*} [Ring 
R] [Ring S] (f : R ->+* S) : map f (cyclotomic n R) = cyclotomic n S
· 使用定理 `Polynomial.isRoot_cyclotomic_iff`：isRoot_cyclotomic_iff [NeZero (n : R)]
 {μ : R} : IsRoot (cyclotomic n R) μ ↔ IsPrimitiveRoot μ n
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
-/
theorem aeval_zeta [IsDomain B] [NeZero (n : B)] :
    aeval (zeta n A B) (cyclotomic n A) = 0 := by
  rw [← eval_map_algebraMap, ← IsRoot.def, map_cyclotomic, isRoot_cyclotomic_iff]
  exact zeta_spec n A B
/-
**IsCyclotomicExtension.zeta_isRoot** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomicExten
sion`。
形式化陈述：zeta_isRoot [IsDomain B] [NeZero (n : B)] : IsRoot (cyclotomic n B) (zeta 
n A B)
参数：n : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `Polynomial.map_cyclotomic`：map_cyclotomic (n : Nat) {R S : Type*} [Ring 
R] [Ring S] (f : R ->+* S) : map f (cyclotomic n R) = cyclotomic n S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsCyclotomicExtension.aeval_zeta`：aeval_zeta [IsDomain B] [NeZero (n : B
)] : aeval (zeta n A B) (cyclotomic n A) = 0
-/
theorem zeta_isRoot [IsDomain B] [NeZero (n : B)] : IsRoot (cyclotomic n B) (zeta n A B) := by
  convert! aeval_zeta n A B using 0
  rw [IsRoot.def, aeval_def, eval₂_eq_eval_map, map_cyclotomic]
/-
**IsCyclotomicExtension.zeta_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomicExtensio
n`。
形式化陈述：zeta_pow : zeta n A B ^ n = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.pow_eq_one`：∀ {M : Type u_1} [inst : CommMonoid M] {ζ : 
M} {k : ℕ}, IsPrimitiveRoot ζ k → ζ ^ k = 1
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
-/
theorem zeta_pow : zeta n A B ^ n = 1 :=
  (zeta_spec n A B).pow_eq_one

end IsCyclotomicExtension

end Zeta

section NoOrder

variable [Field K] [CommRing L] [IsDomain L] [Algebra K L] [IsCyclotomicExtension {n} K L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ n)

namespace IsPrimitiveRoot

variable {C}

/-- The `PowerBasis` given by a primitive root `η`. -/
@[simps!]
/-
**IsPrimitiveRoot.powerBasis** 是 Mathlib 中的一个定义，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：{n : ℕ} →   [NeZero n] →     (K : Type u) →       {L : Type v} →         [
inst : Field K] →           [inst_1 : CommRing L] →             [IsDomain L] →  
             [inst_3 : Algebra K L] → [IsCyclotomicExtension {n} K L] → {ζ : L} 
→ IsPrimitiveRoot ζ n → PowerBasis K L
参数：K : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `PowerBasis` given by a primitive root `η`.
-/
protected noncomputable def powerBasis : PowerBasis K L :=
  -- this is purely an optimization
  letI pb := Algebra.adjoin.powerBasis <| (integral {n} K L).isIntegral ζ
  pb.map <| (Subalgebra.equivOfEq _ _ (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)).trans
    Subalgebra.topEquiv
/-
**IsPrimitiveRoot.powerBasis_gen_mem_adjoin_zeta_sub_one** 是 Mathlib 中的一个定理，位于命名
空间 `IsPrimitiveRoot`。
形式化陈述：powerBasis_gen_mem_adjoin_zeta_sub_one : (hζ.powerBasis K).gen in adjoin K
 ({ζ - 1} : Set L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPrimitiveRoot.powerBasis_gen`：∀ {n : ℕ} [inst : NeZero n] (K : Type u)
 {L : Type v} [inst_1 : Field K] [inst_2 : CommRing L] [inst_3 : IsDomain L]   [
inst_4 : Algebra K L…
· 使用定理 `Algebra.adjoin_singleton_eq_range_aeval`：adjoin_singleton_eq_range_aeval
 (x : A) : adjoin R {x} = (aeval x).range
· 使用定理 `AlgHom.mem_range`：mem_range (φ : A ->ₐ[R] B) {y : B} : y in φ.range ↔ ex
ists x, φ x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
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
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem powerBasis_gen_mem_adjoin_zeta_sub_one :
    (hζ.powerBasis K).gen ∈ adjoin K ({ζ - 1} : Set L) := by
  rw [powerBasis_gen, adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
  exact ⟨X + 1, by simp⟩

/-- The `PowerBasis` given by `η - 1`. -/
@[simps!]
/-
**IsPrimitiveRoot.subOnePowerBasis** 是 Mathlib 中的一个定义，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：subOnePowerBasis : PowerBasis K L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `PowerBasis` given by `η - 1`.
-/
noncomputable def subOnePowerBasis : PowerBasis K L := by
  apply PowerBasis.ofAdjoinEqTop (((integral {n} K L).isIntegral ζ).sub isIntegral_one)
  exact PowerBasis.adjoin_eq_top_of_gen_mem_adjoin (hζ.powerBasis_gen_mem_adjoin_zeta_sub_one _)

variable {K} (C)

-- We are not using @[simps] to avoid a timeout.
/-- The equivalence between `L →ₐ[K] C` and `primitiveRoots n C` given by a primitive root `ζ`. -/
/-
**IsPrimitiveRoot.embeddingsEquivPrimitiveRoots** 是 Mathlib 中的一个定义，位于命名空间 `IsPri
mitiveRoot`。
形式化陈述：embeddingsEquivPrimitiveRoots (C : Type*) [CommRing C] [IsDomain C] [Algeb
ra K C] (hirr : Irreducible (cyclotomic n K)) : (L ->ₐ[K] C) ≃ primitiveRoots n 
C
参数：C : Type*；hirr : Irreducible (cyclotomic n K)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The equivalence between `L →ₐ[K] C` and `primitiveRoots n C` given by a primitiv
e root `ζ`.
-/
noncomputable def embeddingsEquivPrimitiveRoots (C : Type*) [CommRing C] [IsDomain C] [Algebra K C]
    (hirr : Irreducible (cyclotomic n K)) : (L →ₐ[K] C) ≃ primitiveRoots n C :=
  (hζ.powerBasis K).liftEquiv.trans
    { toFun := fun x => by
        haveI := IsCyclotomicExtension.neZero' n K L
        haveI hn := NeZero.of_faithfulSMul K C n
        refine ⟨x.1, ?_⟩
        cases x
        rwa [mem_primitiveRoots (NeZero.pos _), ← isRoot_cyclotomic_iff, IsRoot.def,
          ← map_cyclotomic _ (algebraMap K C), hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
          ← eval₂_eq_eval_map, ← aeval_def]
      invFun := fun x => by
        haveI := IsCyclotomicExtension.neZero' n K L
        haveI hn := NeZero.of_faithfulSMul K C n
        refine ⟨x.1, ?_⟩
        cases x
        rwa [aeval_def, eval₂_eq_eval_map, hζ.powerBasis_gen K, ←
          hζ.minpoly_eq_cyclotomic_of_irreducible hirr, map_cyclotomic, ← IsRoot.def,
          isRoot_cyclotomic_iff, ← mem_primitiveRoots (NeZero.pos _)] }

-- Porting note: renamed argument `φ`: "expected '_' or identifier"
@[simp]
/-
**IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe** 是 Mathlib 中的一个定理，位于命
名空间 `IsPrimitiveRoot`。
形式化陈述：embeddingsEquivPrimitiveRoots_apply_coe (C : Type*) [CommRing C] [IsDomain
 C] [Algebra K C] (hirr : Irreducible (cyclotomic n K)) (φ' : L ->ₐ[K] C) : (hζ.
embeddingsEquivPrimitiveRoots C hirr φ' : C) = φ' ζ
参数：C : Type*；hirr : Irreducible (cyclotomic n K)；φ' : L ->ₐ[K] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem embeddingsEquivPrimitiveRoots_apply_coe (C : Type*) [CommRing C] [IsDomain C] [Algebra K C]
    (hirr : Irreducible (cyclotomic n K)) (φ' : L →ₐ[K] C) :
    (hζ.embeddingsEquivPrimitiveRoots C hirr φ' : C) = φ' ζ :=
  rfl

end IsPrimitiveRoot

namespace IsCyclotomicExtension

variable {K} (L)

/-- If `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the `finrank` of a
cyclotomic extension is `n.totient`. -/
/-
**IsCyclotomicExtension.finrank** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomicExtension
`。
形式化陈述：finrank (hirr : Irreducible (cyclotomic n K)) : finrank K L = n.totient
参数：hirr : Irreducible (cyclotomic n K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.neZero'`：neZero' [IsCyclotomicExtension {n} A B] [
IsDomain B] : NeZero (n : A)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerBasis.finrank`：finrank [StrongRankCondition R] (pb : PowerBasis R S
) : Module.finrank R S = pb.dim
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsPrimitiveRoot.powerBasis_dim`：∀ {n : ℕ} [inst : NeZero n] (K : Type u)
 {L : Type v} [inst_1 : Field K] [inst_2 : CommRing L] [inst_3 : IsDomain L]   [
inst_4 : Algebra K L…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible`：∀ {K : Type u_2} [
inst : Field K] {R : Type u_3} [inst_1 : CommRing R] [IsDomain R] {μ : R} {n : ℕ
}   [inst_3 : Algebra K R],   IsPrimitiveR…
· 使用定理 `Polynomial.natDegree_cyclotomic`：natDegree_cyclotomic (n : Nat) (R : Typ
e*) [Ring R] [Nontrivial R] : (cyclotomic n R).natDegree = Nat.totient n

--- 原说明 ---
If `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the `finrank
` of a
cyclotomic extension is `n.totient`.
-/
theorem finrank (hirr : Irreducible (cyclotomic n K)) : finrank K L = n.totient := by
  have := IsCyclotomicExtension.neZero' n K L
  rw [((zeta_spec n K L).powerBasis K).finrank, IsPrimitiveRoot.powerBasis_dim, ←
    (zeta_spec n K L).minpoly_eq_cyclotomic_of_irreducible hirr, natDegree_cyclotomic]

variable {L} in
/-- If `L` contains both a primitive `p`-th root of unity and `q`-th root of unity, and
`Irreducible (cyclotomic (lcm p q) K)` (in particular for `K = ℚ`), then the `finrank K L` is at
least `(lcm p q).totient`. -/
/-
**IsCyclotomicExtension._root_.IsPrimitiveRoot.lcm_totient_le_finrank** 是 Mathli
b 中的一个定理，位于命名空间 `IsCyclotomicExtension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L` contains both a primitive `p`-th root of unity and `q`-th root of unity, 
and
`Irreducible (cyclotomic (lcm p q) K)` (in particular for `K = ℚ`), then the `fi
nrank K L` is at
least `(lcm p q).totient`.
-/
theorem _root_.IsPrimitiveRoot.lcm_totient_le_finrank [FiniteDimensional K L] {p q : ℕ} {x y : L}
    (hx : IsPrimitiveRoot x p) (hy : IsPrimitiveRoot y q)
    (hirr : Irreducible (cyclotomic (Nat.lcm p q) K)) :
    (Nat.lcm p q).totient ≤ Module.finrank K L := by
  rcases Nat.eq_zero_or_pos p with (rfl | hppos)
  · simp
  rcases Nat.eq_zero_or_pos q with (rfl | hqpos)
  · simp
  let z := x ^ (p / factorizationLCMLeft p q) * y ^ (q / factorizationLCMRight p q)
  let k := PNat.lcm ⟨p, hppos⟩ ⟨q, hqpos⟩
  have : IsPrimitiveRoot z k := hx.pow_mul_pow_lcm hy hppos.ne' hqpos.ne'
  have := IsPrimitiveRoot.adjoin_isCyclotomicExtension K this
  convert! Submodule.finrank_le (Subalgebra.toSubmodule (adjoin K { z }))
  rw [show Nat.lcm p q = (k : ℕ) from rfl] at hirr
  simpa using! (IsCyclotomicExtension.finrank (Algebra.adjoin K {z}) hirr).symm

end IsCyclotomicExtension

end NoOrder

section Norm

namespace IsPrimitiveRoot

section Field

variable {K} [Field K] [NumberField K]

variable (n) in
/-- If an `n`-th cyclotomic extension of `ℚ` contains a primitive `l`-th root of unity, then
`l ∣ 2 * n`. -/
/-
**IsPrimitiveRoot.dvd_of_isCyclotomicExtension** 是 Mathlib 中的一个定理，位于命名空间 `IsPrim
itiveRoot`。
形式化陈述：dvd_of_isCyclotomicExtension [IsCyclotomicExtension {n} Rat K] {ζ : K} {l 
: Nat} (hζ : IsPrimitiveRoot ζ l) (hl : l != 0) : l ∣ 2 * n
参数：hζ : IsPrimitiveRoot ζ l；hl : l != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `IsPrimitiveRoot.lcm_totient_le_finrank`：∀ {K : Type u} {L : Type v} [ins
t : Field K] [inst_1 : CommRing L] [IsDomain L] [inst_3 : Algebra K L]   [Finite
Dimensional K L] {p q : ℕ} {…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `Nat.lcm_pos`：∀ {m n : ℕ}, 0 < m → 0 < n → 0 < m.lcm n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `dvd_lcm_right`：dvd_lcm_right [GCDMonoid α] (a b : α) : b ∣ lcm a b
· 使用定理 `Nat.totient_super_multiplicative`：totient_super_multiplicative (a b : Na
t) : φ a * φ b <= φ (a * b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_le_iff_le_one_right`：mul_le_iff_le_one_right [PosMulMono α] [PosMulR
eflectLE α] (a0 : 0 < a) : a * b <= a ↔ b <= 1
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.totient_pos`：∀ {n : ℕ}, 0 < n.totient ↔ 0 < n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCyclotomicExtension.finrank`：finrank (hirr : Irreducible (cyclotomic n
 K)) : finrank K L = n.totient
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If an `n`-th cyclotomic extension of `ℚ` contains a primitive `l`-th root of uni
ty, then
`l ∣ 2 * n`.
-/
theorem dvd_of_isCyclotomicExtension [IsCyclotomicExtension {n} ℚ K] {ζ : K}
    {l : ℕ} (hζ : IsPrimitiveRoot ζ l) (hl : l ≠ 0) : l ∣ 2 * n := by
  have hl : NeZero l := ⟨hl⟩
  have hroot := IsCyclotomicExtension.zeta_spec n ℚ K
  have key := IsPrimitiveRoot.lcm_totient_le_finrank hζ hroot
    (cyclotomic.irreducible_rat <| Nat.lcm_pos (Nat.pos_of_ne_zero hl.1) (NeZero.pos n))
  rw [IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat (NeZero.pos n))] at key
  rcases _root_.dvd_lcm_right l n with ⟨r, hr⟩
  have ineq := Nat.totient_super_multiplicative n r
  rw [← hr] at ineq
  replace key := (mul_le_iff_le_one_right (Nat.totient_pos.2 (NeZero.pos n))).mp (le_trans ineq key)
  have rpos : 0 < r := by
    refine Nat.pos_of_ne_zero (fun h ↦ ?_)
    simp only [h, mul_zero, _root_.lcm_eq_zero_iff, NeZero.ne _, or_false] at hr
  replace key := (Nat.dvd_prime Nat.prime_two).1 (Nat.dvd_two_of_totient_le_one rpos key)
  rcases key with (key | key)
  · rw [key, mul_one] at hr
    rw [← hr]
    exact dvd_mul_of_dvd_right (_root_.dvd_lcm_left l n) 2
  · rw [key, mul_comm] at hr
    simpa [← hr] using _root_.dvd_lcm_left _ _

/-- If `x` is a root of unity (spelled as `IsOfFinOrder x`) in an `n`-th cyclotomic extension of
`ℚ`, where `n` is odd, and `ζ` is a primitive `n`-th root of unity, then there exist `r`
such that `x = (-ζ)^r`. -/
/-
**IsPrimitiveRoot.exists_neg_pow_of_isOfFinOrder** 是 Mathlib 中的一个定理，位于命名空间 `IsPr
imitiveRoot`。
形式化陈述：exists_neg_pow_of_isOfFinOrder [IsCyclotomicExtension {n} Rat K] (hno : Od
d n) {ζ x : K} (hζ : IsPrimitiveRoot ζ n) (hx : IsOfFinOrder x) : exists r : Nat
, x = (-ζ) ^ r
参数：hno : Odd n；hζ : IsPrimitiveRoot ζ n；hx : IsOfFinOrder x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_eq_neg_one_mul`：neg_eq_neg_one_mul (a : α) : -a = -1 * a
· 使用定理 `Commute.orderOf_mul_eq_mul_orderOf_of_coprime`：orderOf_mul_eq_mul_orderO
f_of_coprime (h : Commute x y) (hco : (orderOf x).Coprime (orderOf y)) : orderOf
 (x * y) = orderOf x * orderOf y
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `orderOf_neg_one`：orderOf_neg_one {R} [Ring R] [Nontrivial R] : orderOf (
-1 : R) = if ringChar R = 2 then 1 else 2
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ringChar.eq_zero`：eq_zero [CharZero R] : ringChar R = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsPrimitiveRoot.eq_orderOf`：eq_orderOf (h : IsPrimitiveRoot ζ k) : k = o
rderOf ζ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsPrimitiveRoot.orderOf`：∀ {M : Type u_1} [inst : CommMonoid M] (ζ : M),
 IsPrimitiveRoot ζ (orderOf ζ)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `isRoot_of_unity_iff`：∀ {n : ℕ},   0 < n →     ∀ (R : Type u_2) [inst : C
ommRing R] [IsDomain R] {ζ : R},       ζ ^ n = 1 ↔ ∃ i ∈ n.divisors, (Polynomial
.cyclotom…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `NeZero.natCast_ne`：natCast_ne (n : Nat) (R) [AddMonoidWithOne R] [h : Ne
Zero (n : R)] : (n : R) != 0
· 使用定理 `IsPrimitiveRoot.dvd_of_isCyclotomicExtension`：dvd_of_isCyclotomicExtensi
on [IsCyclotomicExtension {n} Rat K] {ζ : K} {l : Nat} (hζ : IsPrimitiveRoot ζ l
) (hl : l != 0) : l ∣ 2 * n
· 使用定理 `Polynomial.isRoot_cyclotomic_iff`：isRoot_cyclotomic_iff [NeZero (n : R)]
 {μ : R} : IsRoot (cyclotomic n R) μ ↔ IsPrimitiveRoot μ n
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If `x` is a root of unity (spelled as `IsOfFinOrder x`) in an `n`-th cyclotomic 
extension of
`ℚ`, where `n` is odd, and `ζ` is a primitive `n`-th root of unity, then there e
xist `r`
such that `x = (-ζ)^r`.
-/
theorem exists_neg_pow_of_isOfFinOrder [IsCyclotomicExtension {n} ℚ K]
    (hno : Odd n) {ζ x : K} (hζ : IsPrimitiveRoot ζ n) (hx : IsOfFinOrder x) :
    ∃ r : ℕ, x = (-ζ) ^ r := by
  have hnegζ : IsPrimitiveRoot (-ζ) (2 * n) := by
    convert! IsPrimitiveRoot.orderOf (-ζ)
    rw [neg_eq_neg_one_mul, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
    · simp [hζ.eq_orderOf]
    · simp [← hζ.eq_orderOf, hno]
  obtain ⟨k, hkpos, hkn⟩ := isOfFinOrder_iff_pow_eq_one.1 hx
  obtain ⟨l, hl, hlroot⟩ := (isRoot_of_unity_iff hkpos _).1 hkn
  have hlzero : NeZero l := ⟨fun h ↦ by simp [h] at hl⟩
  have : NeZero (l : K) := ⟨NeZero.natCast_ne l K⟩
  rw [isRoot_cyclotomic_iff] at hlroot
  obtain ⟨a, ha⟩ := hlroot.dvd_of_isCyclotomicExtension n hlzero.1
  replace hlroot : x ^ (2 * n) = 1 := by rw [ha, pow_mul, hlroot.pow_eq_one, one_pow]
  obtain ⟨s, -, hs⟩ := hnegζ.eq_pow_of_pow_eq_one hlroot
  exact ⟨s, hs.symm⟩

/-- If `x` is a root of unity (spelled as `IsOfFinOrder x`) in an `n`-th cyclotomic extension of
`ℚ`, where `n` is odd, and `ζ` is a primitive `n`-th root of unity, then there exists `r < n`
such that `x = ζ^r` or `x = -ζ^r`. -/
/-
**IsPrimitiveRoot.exists_pow_or_neg_mul_pow_of_isOfFinOrder** 是 Mathlib 中的一个定理，位
于命名空间 `IsPrimitiveRoot`。
形式化陈述：exists_pow_or_neg_mul_pow_of_isOfFinOrder [IsCyclotomicExtension {n} Rat K
] (hno : Odd n) {ζ x : K} (hζ : IsPrimitiveRoot ζ n) (hx : IsOfFinOrder x) : exi
sts r : Nat, r < n ∧ (x = ζ ^ r ∨ x = -ζ ^ r)
参数：hno : Odd n；hζ : IsPrimitiveRoot ζ n；hx : IsOfFinOrder x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsPrimitiveRoot.exists_neg_pow_of_isOfFinOrder`：exists_neg_pow_of_isOfFi
nOrder [IsCyclotomicExtension {n} Rat K] (hno : Odd n) {ζ x : K} (hζ : IsPrimiti
veRoot ζ n) (hx : IsOfFinOrder x) : …
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_mod_orderOf`：pow_mod_orderOf (x : G) (n : Nat) : x ^ (n % orderOf x)
 = x ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimitiveRoot.eq_orderOf`：eq_orderOf (h : IsPrimitiveRoot ζ k) : k = o
rderOf ζ
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `neg_pow`：neg_pow (a : R) (n : Nat) : (-a) ^ n = (-1) ^ n * a ^ n
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Odd.neg_one_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistrib
Neg α] {n : ℕ}, Odd n → (-1) ^ n = -1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True

--- 原说明 ---
If `x` is a root of unity (spelled as `IsOfFinOrder x`) in an `n`-th cyclotomic 
extension of
`ℚ`, where `n` is odd, and `ζ` is a primitive `n`-th root of unity, then there e
xists `r < n`
such that `x = ζ^r` or `x = -ζ^r`.
-/
theorem exists_pow_or_neg_mul_pow_of_isOfFinOrder [IsCyclotomicExtension {n} ℚ K]
    (hno : Odd n) {ζ x : K} (hζ : IsPrimitiveRoot ζ n) (hx : IsOfFinOrder x) :
    ∃ r : ℕ, r < n ∧ (x = ζ ^ r ∨ x = -ζ ^ r) := by
  obtain ⟨r, hr⟩ := hζ.exists_neg_pow_of_isOfFinOrder hno hx
  refine ⟨r % n, Nat.mod_lt _ (NeZero.pos _), ?_⟩
  rw [show ζ ^ (r % n) = ζ ^ r from (IsPrimitiveRoot.eq_orderOf hζ).symm ▸ pow_mod_orderOf .., hr]
  rcases Nat.even_or_odd r with (h | h) <;> simp [neg_pow, h.neg_one_pow]

end Field

section CommRing

variable [CommRing L] {ζ : L}
variable {K} [Field K] [Algebra K L]

/-- This mathematically trivial result is complementary to `norm_eq_one` below. -/
/-
**IsPrimitiveRoot.norm_eq_neg_one_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot
`。
形式化陈述：norm_eq_neg_one_pow (hζ : IsPrimitiveRoot ζ 2) [IsDomain L] : norm K ζ = (
-1 : K) ^ finrank K L
参数：hζ : IsPrimitiveRoot ζ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPrimitiveRoot.eq_neg_one_of_two_right`：eq_neg_one_of_two_right [NoZero
Divisors R] {ζ : R} (h : IsPrimitiveRoot ζ 2) : ζ = -1
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `Algebra.norm_algebraMap`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRin
g R] [inst_1 : Ring S] [inst_2 : Algebra R S] [Module.Free R S] (x : R),   (Alge
bra.norm R) (…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
This mathematically trivial result is complementary to `norm_eq_one` below.
-/
theorem norm_eq_neg_one_pow (hζ : IsPrimitiveRoot ζ 2) [IsDomain L] :
    norm K ζ = (-1 : K) ^ finrank K L := by
  rw [hζ.eq_neg_one_of_two_right, show -1 = algebraMap K L (-1) by simp, Algebra.norm_algebraMap]

variable (hζ : IsPrimitiveRoot ζ n)
include hζ

/-- If `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`), the norm of a primitive root is
`1` if `n ≠ 2`. -/
/-
**IsPrimitiveRoot.norm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：norm_eq_one [IsDomain L] [IsCyclotomicExtension {n} K L] (hn : n != 2) (hi
rr : Irreducible (cyclotomic n K)) : norm K ζ = 1
参数：hn : n != 2；hirr : Irreducible (cyclotomic n K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.neZero'`：neZero' [IsCyclotomicExtension {n} A B] [
IsDomain B] : NeZero (n : A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPrimitiveRoot.one_right_iff`：one_right_iff : IsPrimitiveRoot ζ 1 ↔ ζ =
 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `Algebra.norm_algebraMap`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRin
g R] [inst_1 : Ring S] [inst_2 : Algebra R S] [Module.Free R S] (x : R),   (Alge
bra.norm R) (…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.two_le_iff`：∀ (n : ℕ), 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimitiveRoot.powerBasis_gen`：∀ {n : ℕ} [inst : NeZero n] (K : Type u)
 {L : Type v} [inst_1 : Field K] [inst_2 : CommRing L] [inst_3 : IsDomain L]   [
inst_4 : Algebra K L…
· 使用定理 `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`：∀ {R : Type u_1} {S :
 Type u_2} [inst : CommRing R] [inst_1 : Ring S] [inst_2 : Algebra R S] (pb : Po
werBasis R S),   (Algebra.norm R) pb.ge…
· 使用定理 `IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible`：∀ {K : Type u_2} [
inst : Field K] {R : Type u_3} [inst_1 : CommRing R] [IsDomain R] {μ : R} {n : ℕ
}   [inst_3 : Algebra K R],   IsPrimitiveR…
· 使用定理 `Polynomial.cyclotomic_coeff_zero`：cyclotomic_coeff_zero (R : Type*) [Com
mRing R] {n : Nat} (hn : 1 < n) : (cyclotomic n R).coeff 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsPrimitiveRoot.powerBasis_dim`：∀ {n : ℕ} [inst : NeZero n] (K : Type u)
 {L : Type v} [inst_1 : Field K] [inst_2 : CommRing L] [inst_3 : IsDomain L]   [
inst_4 : Algebra K L…
· 使用定理 `Polynomial.natDegree_cyclotomic`：natDegree_cyclotomic (n : Nat) (R : Typ
e*) [Ring R] [Nontrivial R] : (cyclotomic n R).natDegree = Nat.totient n
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
· 使用定理 `Nat.totient_even`：totient_even {n : Nat} (hn : 2 < n) : Even n.totient
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
If `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`), the norm of a pri
mitive root is
`1` if `n ≠ 2`.
-/
theorem norm_eq_one [IsDomain L] [IsCyclotomicExtension {n} K L] (hn : n ≠ 2)
    (hirr : Irreducible (cyclotomic n K)) : norm K ζ = 1 := by
  have := IsCyclotomicExtension.neZero' n K L
  by_cases h1 : n = 1
  · rw [h1, one_right_iff] at hζ
    rw [hζ, show 1 = algebraMap K L 1 by simp, Algebra.norm_algebraMap, one_pow]
  · replace h1 : 2 ≤ n := (two_le_iff n).mpr ⟨NeZero.ne _, h1⟩
    rw [← hζ.powerBasis_gen K, PowerBasis.norm_gen_eq_coeff_zero_minpoly, hζ.powerBasis_gen K,
      ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, cyclotomic_coeff_zero K h1, mul_one,
      hζ.powerBasis_dim K, ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, natDegree_cyclotomic]
    exact (totient_even <| h1.lt_of_ne hn.symm).neg_one_pow

omit [NeZero n] in
/-- If `K` is linearly ordered, the norm of a primitive root is `1` if `n` is odd. -/
/-
**IsPrimitiveRoot.norm_eq_one_of_linearly_ordered** 是 Mathlib 中的一个定理，位于命名空间 `IsP
rimitiveRoot`。
形式化陈述：norm_eq_one_of_linearly_ordered {K : Type*} [Field K] [LinearOrder K] [IsS
trictOrderedRing K] [Algebra K L] (hodd : Odd n) : norm K ζ = 1
参数：hodd : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsPrimitiveRoot.iff_def`：∀ {M : Type u_1} [inst : CommMonoid M] (ζ : M) 
(k : ℕ), IsPrimitiveRoot ζ k ↔ ζ ^ k = 1 ∧ ∀ (l : ℕ), ζ ^ l = 1 → k ∣ l
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Odd.strictMono_pow`：Odd.strictMono_pow (hn : Odd n) : StrictMono fun a :
 R => a ^ n
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Algebra.norm_algebraMap`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRin
g R] [inst_1 : Ring S] [inst_2 : Algebra R S] [Module.Free R S] (x : R),   (Alge
bra.norm R) (…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1

--- 原说明 ---
If `K` is linearly ordered, the norm of a primitive root is `1` if `n` is odd.
-/
theorem norm_eq_one_of_linearly_ordered {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Algebra K L] (hodd : Odd n) :
    norm K ζ = 1 := by
  have hz := congr_arg (norm K) ((IsPrimitiveRoot.iff_def _ n).1 hζ).1
  rw [← (algebraMap K L).map_one, Algebra.norm_algebraMap, one_pow, map_pow, ← one_pow n] at hz
  exact StrictMono.injective hodd.strictMono_pow hz
/-
**IsPrimitiveRoot.norm_of_cyclotomic_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `IsPr
imitiveRoot`。
形式化陈述：norm_of_cyclotomic_irreducible [IsDomain L] [IsCyclotomicExtension {n} K L
] (hirr : Irreducible (cyclotomic n K)) : norm K ζ = ite (n = 2) (-1) 1
参数：hirr : Irreducible (cyclotomic n K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `IsPrimitiveRoot.norm_eq_neg_one_pow`：norm_eq_neg_one_pow (hζ : IsPrimiti
veRoot ζ 2) [IsDomain L] : norm K ζ = (-1 : K) ^ finrank K L
· 使用定理 `IsCyclotomicExtension.finrank`：finrank (hirr : Irreducible (cyclotomic n
 K)) : finrank K L = n.totient
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `IsPrimitiveRoot.norm_eq_one`：norm_eq_one [IsDomain L] [IsCyclotomicExten
sion {n} K L] (hn : n != 2) (hirr : Irreducible (cyclotomic n K)) : norm K ζ = 1
-/
theorem norm_of_cyclotomic_irreducible [IsDomain L] [IsCyclotomicExtension {n} K L]
    (hirr : Irreducible (cyclotomic n K)) : norm K ζ = ite (n = 2) (-1) 1 := by
  split_ifs with hn
  · subst hn
    rw [norm_eq_neg_one_pow (K := K) hζ, IsCyclotomicExtension.finrank _ hirr]
    norm_cast
  · exact hζ.norm_eq_one hn hirr

end CommRing

section Field

variable [Field L] {ζ : L}
variable {K} [Field K] [Algebra K L]

section
variable (hζ : IsPrimitiveRoot ζ n)
include hζ

/-- If `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the norm of
`ζ - 1` is `eval 1 (cyclotomic n ℤ)`. -/
/-
**IsPrimitiveRoot.sub_one_norm_eq_eval_cyclotomic** 是 Mathlib 中的一个定理，位于命名空间 `IsP
rimitiveRoot`。
形式化陈述：sub_one_norm_eq_eval_cyclotomic [IsCyclotomicExtension {n} K L] (h : 2 < n
) (hirr : Irreducible (cyclotomic n K)) : norm K (ζ - 1) = ↑(eval 1 (cyclotomic 
n Int))
参数：h : 2 < n；hirr : Irreducible (cyclotomic n K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.neZero'`：neZero' [IsCyclotomicExtension {n} A B] [
IsDomain B] : NeZero (n : A)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsAlgClosed.exists_root`：exists_root [IsAlgClosed k] (p : k[X]) (hp : p.
degree != 0) : exists x, IsRoot p x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Polynomial.degree_cyclotomic_pos`：degree_cyclotomic_pos (n : Nat) (R : T
ype*) (hpos : 0 < n) [Ring R] [Nontrivial R] : 0 < (cyclotomic n R).degree
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsCyclotomicExtension.finiteDimensional`：finiteDimensional (C : Type z) 
[Finite S] [CommRing C] [Algebra K C] [IsDomain C] [IsCyclotomicExtension S K C]
 : FiniteDimensional K C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsCyclotomicExtension.isGalois`：isGalois [IsCyclotomicExtension S K L] :
 IsGalois K L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_eq_prod_embeddings`：norm_eq_prod_embeddings [Algebra.IsSepa
rable K L] [IsAlgClosed E] (x : L) : algebraMap K E (norm K x) = ∏ σ : L ->ₐ[K] 
E, σ x
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
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
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
If `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the norm of
`ζ - 1` is `eval 1 (cyclotomic n ℤ)`.
-/
theorem sub_one_norm_eq_eval_cyclotomic [IsCyclotomicExtension {n} K L] (h : 2 < n)
    (hirr : Irreducible (cyclotomic n K)) : norm K (ζ - 1) = ↑(eval 1 (cyclotomic n ℤ)) := by
  have := IsCyclotomicExtension.neZero' n K L
  let E := AlgebraicClosure L
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ (degree_cyclotomic_pos n E (NeZero.pos _)).ne.symm
  apply (algebraMap K E).injective
  let := IsCyclotomicExtension.finiteDimensional {n} K L
  let := IsCyclotomicExtension.isGalois {n} K L
  rw [norm_eq_prod_embeddings]
  conv_lhs =>
    congr
    rfl
    ext
    rw [← neg_sub, map_neg, map_sub, map_one, neg_eq_neg_one_mul]
  rw [prod_mul_distrib, prod_const, Finset.card_univ, AlgHom.card,
    IsCyclotomicExtension.finrank L hirr, (totient_even h).neg_one_pow, one_mul]
  have Hprod : (Finset.univ.prod fun σ : L →ₐ[K] E => 1 - σ ζ) = eval 1 (cyclotomic' n E) := by
    rw [cyclotomic', eval_prod, ← @Finset.prod_attach E E, ← univ_eq_attach]
    refine Fintype.prod_equiv (hζ.embeddingsEquivPrimitiveRoots E hirr) _ _ fun σ => ?_
    simp
  have : NeZero (n : E) := NeZero.of_faithfulSMul K _ n
  rw [Hprod, cyclotomic', ← cyclotomic_eq_prod_X_sub_primitiveRoots (isRoot_cyclotomic_iff.1 hz),
    ← map_cyclotomic_int, _root_.map_intCast, ← Int.cast_one, eval_intCast_map, eq_intCast,
    Int.cast_id]

/-- If `IsPrimePow n`, `n ≠ 2` and `Irreducible (cyclotomic n K)` (in particular for
`K = ℚ`), then the norm of `ζ - 1` is `n.minFac`. -/
/-
**IsPrimitiveRoot.sub_one_norm_isPrimePow** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitive
Root`。
形式化陈述：sub_one_norm_isPrimePow (hn : IsPrimePow n) [IsCyclotomicExtension {n} K L
] (hirr : Irreducible (cyclotomic n K)) (h : n != 2) : norm K (ζ - 1) = n.minFac
参数：hn : IsPrimePow n；hirr : Irreducible (cyclotomic n K)；h : n != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `IsPrimePow.one_lt`：IsPrimePow.one_lt {n : Nat} (h : IsPrimePow n) : 1 < 
n
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `IsPrimePow.ne_one`：IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n != 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPrimitiveRoot.sub_one_norm_eq_eval_cyclotomic`：sub_one_norm_eq_eval_cy
clotomic [IsCyclotomicExtension {n} K L] (h : 2 < n) (hirr : Irreducible (cyclot
omic n K)) : norm K (ζ - 1) = ↑(eval …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimePow.minFac_pow_factorization_eq`：IsPrimePow.minFac_pow_factorizat
ion_eq {n : Nat} (hn : IsPrimePow n) : n.minFac ^ n.factorization n.minFac = n
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_toFun`：∀ {α : Type u_9} {M : Type u_10} [inst : Zero
 M] (self : α →₀ M) (a : α), a ∈ self.support ↔ self.toFun a ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.mem_primeFactors_iff_mem_primeFactorsList`：mem_primeFactors_iff_mem_
primeFactorsList : p in n.primeFactors ↔ p in n.primeFactorsList
· 使用定理 `Nat.mem_primeFactorsList`：mem_primeFactorsList {n p} (hn : n != 0) : p i
n primeFactorsList n ↔ Prime p ∧ p ∣ n
· 使用定理 `IsPrimePow.ne_zero`：IsPrimePow.ne_zero [IsReduced R] {n : R} (h : IsPrim
ePow n) : n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.eval_one_cyclotomic_prime_pow`：eval_one_cyclotomic_prime_pow 
{R : Type*} [CommRing R] {p : Nat} (k : Nat) [hn : Fact p.Prime] : eval 1 (cyclo
tomic (p ^ (k + 1)) R) = p
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `IsPrimePow n`, `n ≠ 2` and `Irreducible (cyclotomic n K)` (in particular for
`K = ℚ`), then the norm of `ζ - 1` is `n.minFac`.
-/
theorem sub_one_norm_isPrimePow (hn : IsPrimePow n) [IsCyclotomicExtension {n} K L]
    (hirr : Irreducible (cyclotomic n K)) (h : n ≠ 2) : norm K (ζ - 1) = n.minFac := by
  have := (lt_of_le_of_ne (succ_le_of_lt (IsPrimePow.one_lt hn)) h.symm)
  let hprime : Fact n.minFac.Prime := ⟨minFac_prime (IsPrimePow.ne_one hn)⟩
  rw [sub_one_norm_eq_eval_cyclotomic hζ this hirr]
  nth_rw 1 [← IsPrimePow.minFac_pow_factorization_eq hn]
  obtain ⟨k, hk⟩ : ∃ k, n.factorization n.minFac = k + 1 :=
    exists_eq_succ_of_ne_zero
      ((n.factorization.mem_support_toFun n.minFac).1 <|
        mem_primeFactors_iff_mem_primeFactorsList.2 <|
          (mem_primeFactorsList (IsPrimePow.ne_zero hn)).2 ⟨hprime.out, minFac_dvd _⟩)
  simp [hk]

end

variable {A}

/-
**IsPrimitiveRoot.minpoly_sub_one_eq_cyclotomic_comp** 是 Mathlib 中的一个定理，位于命名空间 `
IsPrimitiveRoot`。
形式化陈述：minpoly_sub_one_eq_cyclotomic_comp [Algebra K A] [IsDomain A] {ζ : A} [IsC
yclotomicExtension {n} K A] (hζ : IsPrimitiveRoot ζ n) (h : Irreducible (Polynom
ial.cyclotomic n K)) : minpoly K (ζ - 1) = (cyclotomic n K).comp (X + 1)
参数：hζ : IsPrimitiveRoot ζ n；h : Irreducible (Polynomial.cyclotomic n K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.neZero'`：neZero' [IsCyclotomicExtension {n} A B] [
IsDomain B] : NeZero (n : A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
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
· 使用定理 `minpoly.add_algebraMap`：add_algebraMap {B : Type*} [CommRing B] [Algebra
 A B] (x : B) (a : A) : minpoly A (x + algebraMap A B a) = (minpoly A x).comp (X
 - C a)
· 使用定理 `IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible`：∀ {K : Type u_2} [
inst : Field K] {R : Type u_3} [inst_1 : CommRing R] [IsDomain R] {μ : R} {n : ℕ
}   [inst_3 : Algebra K R],   IsPrimitiveR…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
-/
theorem minpoly_sub_one_eq_cyclotomic_comp [Algebra K A] [IsDomain A] {ζ : A}
    [IsCyclotomicExtension {n} K A] (hζ : IsPrimitiveRoot ζ n)
    (h : Irreducible (Polynomial.cyclotomic n K)) :
    minpoly K (ζ - 1) = (cyclotomic n K).comp (X + 1) := by
  have := IsCyclotomicExtension.neZero' n K A
  rw [show ζ - 1 = ζ + algebraMap K A (-1) by simp [sub_eq_add_neg],
    minpoly.add_algebraMap ζ,
    hζ.minpoly_eq_cyclotomic_of_irreducible h]
  simp

open scoped Cyclotomic

/-- If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `p ^ (k - s + 1) ≠ 2`. See the next lemmas
for similar results. -/
/-
**IsPrimitiveRoot.norm_pow_sub_one_of_prime_pow_ne_two** 是 Mathlib 中的一个定理，位于命名空间
 `IsPrimitiveRoot`。
形式化陈述：norm_pow_sub_one_of_prime_pow_ne_two {k s : Nat} (hζ : IsPrimitiveRoot ζ (
p ^ (k + 1))) [hpri : Fact p.Prime] [IsCyclotomicExtension {p ^ (k + 1)} K L] (h
irr : Irreducible (cyclotomic (p ^ (k + 1)) K)) (hs : s <= k) (htwo : p ^ (k - s
 + 1) != 2) : norm K (ζ ^ p ^ s - 1) = (p : K) ^ p ^ s
参数：hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；k + 1；hirr : Irreducible (cyclotomic (p 
^ (k + 1)) K)；hs : s <= k；htwo : p ^ (k - s + 1) != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.cyclotomic_irreducible_pow_of_irreducible_pow`：cyclotomic_irr
educible_pow_of_irreducible_pow {p : Nat} (hp : Nat.Prime p) {R} [CommRing R] [I
sDomain R] {n m : Nat} (hmn : m <= n) (h : Irr…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `IsPrimitiveRoot.pow`：pow {n : Nat} {a b : Nat} (hn : 0 < n) (h : IsPrimi
tiveRoot ζ n) (hprod : n = a * b) : IsPrimitiveRoot (ζ ^ a) b
· 使用定理 `Nat.pos_of_neZero`：∀ (n : ℕ) [NeZero n], 0 < n
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IntermediateField.adjoin_simple_le_iff`：adjoin_simple_le_iff {K : Interm
ediateField F E} : F⟮α⟯ <= K ↔ α in K
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p
` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `p ^ (k - s + 1) ≠ 2`. Se
e the next lemmas
for similar results.
-/
theorem norm_pow_sub_one_of_prime_pow_ne_two {k s : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    [hpri : Fact p.Prime] [IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K)) (hs : s ≤ k)
    (htwo : p ^ (k - s + 1) ≠ 2) : norm K (ζ ^ p ^ s - 1) = (p : K) ^ p ^ s := by
  have hirr₁ : Irreducible (cyclotomic (p ^ (k - s + 1)) K) :=
    cyclotomic_irreducible_pow_of_irreducible_pow hpri.1 (by lia) hirr
  set η := ζ ^ p ^ s - 1
  let η₁ : K⟮η⟯ := IntermediateField.AdjoinSimple.gen K η
  have hη : IsPrimitiveRoot (η + 1) (p ^ (k + 1 - s)) := by
    rw [sub_add_cancel]
    refine IsPrimitiveRoot.pow (pos_of_neZero (p ^ (k + 1))) hζ ?_
    rw [← pow_add, add_comm s, Nat.sub_add_cancel (le_trans hs (Nat.le_succ k))]
  have : IsCyclotomicExtension {p ^ (k - s + 1)} K K⟮η⟯ := by
    have HKη : K⟮η⟯ = K⟮η + 1⟯ := by
      refine le_antisymm ?_ ?_
      all_goals rw [IntermediateField.adjoin_simple_le_iff]
      · nth_rw 2 [← add_sub_cancel_right η 1]
        exact sub_mem (IntermediateField.mem_adjoin_simple_self K (η + 1)) (one_mem _)
      · exact add_mem (IntermediateField.mem_adjoin_simple_self K η) (one_mem _)
    rw [HKη]
    have H := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((integral {p ^ (k + 1)} K L).isIntegral (η + 1)).isAlgebraic
    refine IsCyclotomicExtension.equiv _ _ _ (h := ?_) (.refl : K⟮η + 1⟯.toSubalgebra ≃ₐ[K] _)
    rw [H]
    have hη' : IsPrimitiveRoot (η + 1) (p ^ (k + 1 - s)) := by simpa using hη
    convert! hη'.adjoin_isCyclotomicExtension K using 1
    rw [Nat.sub_add_comm hs]
  replace hη : IsPrimitiveRoot (η₁ + 1) (p ^ (k - s + 1)) := by
    apply coe_submonoidClass_iff.1
    convert! hη using 1
    rw [Nat.sub_add_comm hs]
  have := IsCyclotomicExtension.finiteDimensional {p ^ (k + 1)} K L
  have := IsCyclotomicExtension.isGalois {p ^ (k + 1)} K L
  rw [norm_eq_norm_adjoin K]
  have H := hη.sub_one_norm_isPrimePow ?_ hirr₁ htwo
  swap; · exact hpri.1.isPrimePow.pow (Nat.succ_ne_zero _)
  rw [add_sub_cancel_right] at H
  rw [H]
  congr
  · rw [Nat.pow_minFac, hpri.1.minFac_eq]
    exact Nat.succ_ne_zero _
  have := Module.finrank_mul_finrank K K⟮η⟯ L
  rw [IsCyclotomicExtension.finrank L hirr, IsCyclotomicExtension.finrank K⟮η⟯ hirr₁,
    Nat.totient_prime_pow hpri.out (k - s).succ_pos, Nat.totient_prime_pow hpri.out k.succ_pos,
    mul_comm _ (p - 1), mul_assoc, mul_comm (p ^ (k.succ - 1))] at this
  replace this := mul_left_cancel₀ (tsub_pos_iff_lt.2 hpri.out.one_lt).ne' this
  have Hex : k.succ - 1 = (k - s).succ - 1 + s := by
    simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
    exact (Nat.sub_add_cancel hs).symm
  rw [Hex, pow_add] at this
  exact mul_left_cancel₀ (pow_ne_zero _ hpri.out.ne_zero) this

/-- If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `p ≠ 2`. -/
/-
**IsPrimitiveRoot.norm_pow_sub_one_of_prime_ne_two** 是 Mathlib 中的一个定理，位于命名空间 `Is
PrimitiveRoot`。
形式化陈述：norm_pow_sub_one_of_prime_ne_two {k : Nat} (hζ : IsPrimitiveRoot ζ (p ^ (k
 + 1))) [hpri : Fact p.Prime] [IsCyclotomicExtension {p ^ (k + 1)} K L] (hirr : 
Irreducible (cyclotomic (p ^ (k + 1)) K)) {s : Nat} (hs : s <= k) (hodd : p != 2
) : norm K (ζ ^ p ^ s - 1) = (p : K) ^ p ^ s
参数：hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；k + 1；hirr : Irreducible (cyclotomic (p 
^ (k + 1)) K)；hs : s <= k；hodd : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.norm_pow_sub_one_of_prime_pow_ne_two`：norm_pow_sub_one_o
f_prime_pow_ne_two {k s : Nat} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) [hpri : Fa
ct p.Prime] [IsCyclotomicExtension {p ^ (k…
· 使用定理 `eq_of_prime_pow_eq`：eq_of_prime_pow_eq (hp₁ : Prime p₁) (hp₂ : Prime p₂)
 (hk₁ : 0 < k₁) (h : p₁ ^ k₁ = p₂ ^ k₂) : p₁ = p₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a

--- 原说明 ---
If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p
` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `p ≠ 2`.
-/
theorem norm_pow_sub_one_of_prime_ne_two {k : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    [hpri : Fact p.Prime] [IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K)) {s : ℕ} (hs : s ≤ k) (hodd : p ≠ 2) :
    norm K (ζ ^ p ^ s - 1) = (p : K) ^ p ^ s := by
  refine hζ.norm_pow_sub_one_of_prime_pow_ne_two hirr hs fun h => ?_
  rw [← pow_one 2] at h
  replace h :=
    eq_of_prime_pow_eq (prime_iff.1 hpri.out) (prime_iff.1 Nat.prime_two) (k - s).succ_pos h
  exact hodd h

/-- If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is an odd
prime, then the norm of `ζ - 1` is `p`. -/
/-
**IsPrimitiveRoot.norm_sub_one_of_prime_ne_two** 是 Mathlib 中的一个定理，位于命名空间 `IsPrim
itiveRoot`。
形式化陈述：norm_sub_one_of_prime_ne_two {k : Nat} (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 
1))) [hpri : Fact p.Prime] [IsCyclotomicExtension {p ^ (k + 1)} K L] (hirr : Irr
educible (cyclotomic (p ^ (k + 1)) K)) (h : p != 2) : norm K (ζ - 1) = p
参数：hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))；k + 1；hirr : Irreducible (cyclotomic (p
 ^ (k + 1)) K)；h : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `IsPrimitiveRoot.norm_pow_sub_one_of_prime_ne_two`：norm_pow_sub_one_of_pr
ime_ne_two {k : Nat} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) [hpri : Fact p.Prime
] [IsCyclotomicExtension {p ^ (k + 1)}…
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n

--- 原说明 ---
If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p
` is an odd
prime, then the norm of `ζ - 1` is `p`.
-/
theorem norm_sub_one_of_prime_ne_two {k : ℕ} (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1)))
    [hpri : Fact p.Prime] [IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K)) (h : p ≠ 2) : norm K (ζ - 1) = p := by
  simpa using hζ.norm_pow_sub_one_of_prime_ne_two hirr k.zero_le h

/-- If `Irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `ζ - 1` is `p`. -/
/-
**IsPrimitiveRoot.norm_sub_one_of_prime_ne_two'** 是 Mathlib 中的一个定理，位于命名空间 `IsPri
mitiveRoot`。
形式化陈述：norm_sub_one_of_prime_ne_two' [hpri : Fact p.Prime] [hcyc : IsCyclotomicEx
tension {p} K L] (hζ : IsPrimitiveRoot ζ p) (hirr : Irreducible (cyclotomic p K)
) (h : p != 2) : norm K (ζ - 1) = p
参数：hζ : IsPrimitiveRoot ζ p；hirr : Irreducible (cyclotomic p K)；h : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two`：norm_sub_one_of_prime_ne_t
wo {k : Nat} (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) [hpri : Fact p.Prime] [IsCy
clotomicExtension {p ^ (k + 1)} K …

--- 原说明 ---
If `Irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd 
prime,
then the norm of `ζ - 1` is `p`.
-/
theorem norm_sub_one_of_prime_ne_two' [hpri : Fact p.Prime]
    [hcyc : IsCyclotomicExtension {p} K L] (hζ : IsPrimitiveRoot ζ p)
    (hirr : Irreducible (cyclotomic p K)) (h : p ≠ 2) : norm K (ζ - 1) = p := by
  replace hirr : Irreducible (cyclotomic (p ^ (0 + 1)) K) := by simp [hirr]
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simp [hζ]
  have : IsCyclotomicExtension {p ^ (0 + 1)} K L := by simp [hcyc]
  simpa using norm_sub_one_of_prime_ne_two hζ hirr h

/-- If `Irreducible (cyclotomic (2 ^ (k + 1)) K)` (in particular for `K = ℚ`), then the norm of
`ζ ^ (2 ^ k) - 1` is `(-2) ^ (2 ^ k)`. -/
/-
**IsPrimitiveRoot.norm_pow_sub_one_two** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoo
t`。
形式化陈述：norm_pow_sub_one_two {k : Nat} (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) [IsC
yclotomicExtension {2 ^ (k + 1)} K L] (hirr : Irreducible (cyclotomic (2 ^ (k + 
1)) K)) : norm K (ζ ^ 2 ^ k - 1) = (-2 : K) ^ 2 ^ k
参数：hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))；k + 1；hirr : Irreducible (cyclotomic (2 
^ (k + 1)) K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.pow_of_dvd`：pow_of_dvd (h : IsPrimitiveRoot ζ k) {p : Na
t} (hp : p != 0) (hdiv : p ∣ k) : IsPrimitiveRoot (ζ ^ p) (k / p)
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
If `Irreducible (cyclotomic (2 ^ (k + 1)) K)` (in particular for `K = ℚ`), then 
the norm of
`ζ ^ (2 ^ k) - 1` is `(-2) ^ (2 ^ k)`.
-/
theorem norm_pow_sub_one_two {k : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    [IsCyclotomicExtension {2 ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (2 ^ (k + 1)) K)) :
    norm K (ζ ^ 2 ^ k - 1) = (-2 : K) ^ 2 ^ k := by
  have := hζ.pow_of_dvd
    (fun h => two_ne_zero (eq_zero_of_pow_eq_zero h)) (pow_dvd_pow 2 (le_succ k))
  rw [Nat.pow_div (le_succ k) zero_lt_two, Nat.succ_sub (le_refl k), Nat.sub_self, pow_one] at this
  have H : (-1 : L) - (1 : L) = algebraMap K L (-2) := by
    simp only [map_neg, map_ofNat]
    ring
  replace hirr : Irreducible (cyclotomic (2 ^ (k + 1)) K) := by simp [hirr]
  rw [this.eq_neg_one_of_two_right, H, Algebra.norm_algebraMap,
    IsCyclotomicExtension.finrank L hirr, totient_prime_pow Nat.prime_two (zero_lt_succ k),
    succ_sub_succ_eq_sub, tsub_zero]
  simp

/-- If `Irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is at least `2`,
then the norm of `ζ - 1` is `2`. -/
/-
**IsPrimitiveRoot.norm_sub_one_two** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：norm_sub_one_two {k : Nat} (hζ : IsPrimitiveRoot ζ (2 ^ k)) (hk : 2 <= k) 
[H : IsCyclotomicExtension {2 ^ k} K L] (hirr : Irreducible (cyclotomic (2 ^ k) 
K)) : norm K (ζ - 1) = 2
参数：hζ : IsPrimitiveRoot ζ (2 ^ k)；hk : 2 <= k；hirr : Irreducible (cyclotomic (2 
^ k) K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.pow_lt_pow_right`：∀ {a m n : ℕ}, 1 < a → m < n → a ^ m < a ^ n
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.eval_one_cyclotomic_prime_pow`：eval_one_cyclotomic_prime_pow 
{R : Type*} [CommRing R] {p : Nat} (k : Nat) [hn : Fact p.Prime] : eval 1 (cyclo
tomic (p ^ (k + 1)) R) = p
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `IsPrimitiveRoot.sub_one_norm_eq_eval_cyclotomic`：sub_one_norm_eq_eval_cy
clotomic [IsCyclotomicExtension {n} K L] (h : 2 < n) (hirr : Irreducible (cyclot
omic n K)) : norm K (ζ - 1) = ↑(eval …
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)

--- 原说明 ---
If `Irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is a
t least `2`,
then the norm of `ζ - 1` is `2`.
-/
theorem norm_sub_one_two {k : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ k)) (hk : 2 ≤ k)
    [H : IsCyclotomicExtension {2 ^ k} K L] (hirr : Irreducible (cyclotomic (2 ^ k) K)) :
    norm K (ζ - 1) = 2 := by
  have : 2 < 2 ^ k := by
    nth_rw 1 [← pow_one 2]
    exact Nat.pow_lt_pow_right one_lt_two (lt_of_lt_of_le one_lt_two hk)
  replace hirr : Irreducible (cyclotomic (2 ^ k) K) := by simp [hirr]
  replace hζ : IsPrimitiveRoot ζ (2 ^ k) := by simp [hζ]
  obtain ⟨k₁, hk₁⟩ := exists_eq_succ_of_ne_zero (lt_of_lt_of_le zero_lt_two hk).ne.symm
  simpa [hk₁] using sub_one_norm_eq_eval_cyclotomic hζ this hirr

/-- If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `k ≠ 0` and `s ≤ k`. -/
/-
**IsPrimitiveRoot.norm_pow_sub_one_eq_prime_pow_of_ne_zero** 是 Mathlib 中的一个定理，位于
命名空间 `IsPrimitiveRoot`。
形式化陈述：norm_pow_sub_one_eq_prime_pow_of_ne_zero {k s : Nat} (hζ : IsPrimitiveRoot
 ζ (p ^ (k + 1))) [hpri : Fact p.Prime] [hcycl : IsCyclotomicExtension {p ^ (k +
 1)} K L] (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K)) (hs : s <= k) (hk : 
k != 0) : norm K (ζ ^ p ^ s - 1) = (p : K) ^ p ^ s
参数：hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；k + 1；hirr : Irreducible (cyclotomic (p 
^ (k + 1)) K)；hs : s <= k；hk : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.pow_eq_iff`：∀ {p a k : ℕ}, Nat.Prime p → (a ^ k = p ↔ a = p ∧ 
k = 1)
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.sub_eq_zero_iff_le`：∀ {n m : ℕ}, n - m = 0 ↔ n ≤ m
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsPrimitiveRoot.norm_pow_sub_one_two`：norm_pow_sub_one_two {k : Nat} (hζ
 : IsPrimitiveRoot ζ (2 ^ (k + 1))) [IsCyclotomicExtension {2 ^ (k + 1)} K L] (h
irr : Irreducible (cycloto…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `neg_eq_neg_one_mul`：neg_eq_neg_one_mul (a : α) : -a = -1 * a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用引理 `neg_one_sq`：neg_one_sq : (-1 : R) ^ 2 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsPrimitiveRoot.norm_pow_sub_one_of_prime_pow_ne_two`：norm_pow_sub_one_o
f_prime_pow_ne_two {k s : Nat} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) [hpri : Fa
ct p.Prime] [IsCyclotomicExtension {p ^ (k…

--- 原说明 ---
If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p
` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `k ≠ 0` and `s ≤ k`.
-/
theorem norm_pow_sub_one_eq_prime_pow_of_ne_zero {k s : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    [hpri : Fact p.Prime] [hcycl : IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K)) (hs : s ≤ k) (hk : k ≠ 0) :
    norm K (ζ ^ p ^ s - 1) = (p : K) ^ p ^ s := by
  by_cases htwo : p ^ (k - s + 1) = 2
  · obtain ⟨hp, hks⟩ := (Nat.prime_two.pow_eq_iff).1 htwo
    simp only [add_eq_right] at hks
    replace hs : s = k := le_antisymm hs (Nat.sub_eq_zero_iff_le.mp hks)
    simp only [hp, hs] at hζ hirr hcycl ⊢
    obtain ⟨k₁, hk₁⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [hζ.norm_pow_sub_one_two hirr, hk₁, _root_.pow_succ', pow_mul, neg_eq_neg_one_mul,
      mul_pow, neg_one_sq, one_mul, ← pow_mul, ← _root_.pow_succ']
    simp
  · exact hζ.norm_pow_sub_one_of_prime_pow_ne_two hirr hs htwo

end Field

end IsPrimitiveRoot

namespace IsCyclotomicExtension

open IsPrimitiveRoot

variable {K} (L) [Field K] [Field L] [Algebra K L]

/-- If `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`), the norm of `zeta n K L` is `1`
if `n` is odd. -/
/-
**IsCyclotomicExtension.norm_zeta_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomic
Extension`。
形式化陈述：norm_zeta_eq_one [IsCyclotomicExtension {n} K L] (hn : n != 2) (hirr : Irr
educible (cyclotomic n K)) : norm K (zeta n K L) = 1
参数：hn : n != 2；hirr : Irreducible (cyclotomic n K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.norm_eq_one`：norm_eq_one [IsDomain L] [IsCyclotomicExten
sion {n} K L] (hn : n != 2) (hirr : Irreducible (cyclotomic n K)) : norm K ζ = 1
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R

--- 原说明 ---
If `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`), the norm of `zeta
 n K L` is `1`
if `n` is odd.
-/
theorem norm_zeta_eq_one [IsCyclotomicExtension {n} K L] (hn : n ≠ 2)
    (hirr : Irreducible (cyclotomic n K)) : norm K (zeta n K L) = 1 :=
  (zeta_spec n K L).norm_eq_one hn hirr

/-- If `IsPrimePow n`, `n ≠ 2` and `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`),
then the norm of `zeta n K L - 1` is `n.minFac`. -/
/-
**IsCyclotomicExtension.norm_zeta_sub_one_of_isPrimePow** 是 Mathlib 中的一个定理，位于命名空
间 `IsCyclotomicExtension`。
形式化陈述：norm_zeta_sub_one_of_isPrimePow (hn : IsPrimePow n) [IsCyclotomicExtension
 {n} K L] (hirr : Irreducible (cyclotomic n K)) (h : n != 2) : norm K (zeta n K 
L - 1) = n.minFac
参数：hn : IsPrimePow n；hirr : Irreducible (cyclotomic n K)；h : n != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.sub_one_norm_isPrimePow`：sub_one_norm_isPrimePow (hn : I
sPrimePow n) [IsCyclotomicExtension {n} K L] (hirr : Irreducible (cyclotomic n K
)) (h : n != 2) : norm K (ζ -…
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n

--- 原说明 ---
If `IsPrimePow n`, `n ≠ 2` and `Irreducible (cyclotomic n K)` (in particular for
 `K = ℚ`),
then the norm of `zeta n K L - 1` is `n.minFac`.
-/
theorem norm_zeta_sub_one_of_isPrimePow (hn : IsPrimePow n) [IsCyclotomicExtension {n} K L]
    (hirr : Irreducible (cyclotomic n K)) (h : n ≠ 2) :
    norm K (zeta n K L - 1) = n.minFac :=
  (zeta_spec n K L).sub_one_norm_isPrimePow hn hirr h

/-- If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `(zeta (p ^ (k + 1)) K L) ^ (p ^ s) - 1` is `p ^ (p ^ s)`
if `p ^ (k - s + 1) ≠ 2`. -/
/-
**IsCyclotomicExtension.norm_zeta_pow_sub_one_of_prime_pow_ne_two** 是 Mathlib 中的
一个定理，位于命名空间 `IsCyclotomicExtension`。
形式化陈述：norm_zeta_pow_sub_one_of_prime_pow_ne_two {k : Nat} [Fact p.Prime] [IsCycl
otomicExtension {p ^ (k + 1)} K L] (hirr : Irreducible (cyclotomic (p ^ (k + 1))
 K)) {s : Nat} (hs : s <= k) (htwo : p ^ (k - s + 1) != 2) : norm K (zeta (p ^ (
k + 1)) K L ^ p ^ s - 1) = (p : K) ^ p ^ s
参数：k + 1；hirr : Irreducible (cyclotomic (p ^ (k + 1)) K)；hs : s <= k；htwo : p ^ 
(k - s + 1) != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.norm_pow_sub_one_of_prime_pow_ne_two`：norm_pow_sub_one_o
f_prime_pow_ne_two {k s : Nat} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) [hpri : Fa
ct p.Prime] [IsCyclotomicExtension {p ^ (k…
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n

--- 原说明 ---
If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p
` is a prime,
then the norm of `(zeta (p ^ (k + 1)) K L) ^ (p ^ s) - 1` is `p ^ (p ^ s)`
if `p ^ (k - s + 1) ≠ 2`.
-/
theorem norm_zeta_pow_sub_one_of_prime_pow_ne_two {k : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K)) {s : ℕ} (hs : s ≤ k)
    (htwo : p ^ (k - s + 1) ≠ 2) :
    norm K (zeta (p ^ (k + 1)) K L ^ p ^ s - 1) = (p : K) ^ p ^ s :=
  (zeta_spec _ K L).norm_pow_sub_one_of_prime_pow_ne_two hirr hs htwo

/-- If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is an odd
prime, then the norm of `zeta (p ^ (k + 1)) K L - 1` is `p`. -/
/-
**IsCyclotomicExtension.norm_zeta_pow_sub_one_of_prime_ne_two** 是 Mathlib 中的一个定理
，位于命名空间 `IsCyclotomicExtension`。
形式化陈述：norm_zeta_pow_sub_one_of_prime_ne_two {k : Nat} [Fact p.Prime] [IsCyclotom
icExtension {p ^ (k + 1)} K L] (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K))
 (h : p != 2) : norm K (zeta (p ^ (k + 1)) K L - 1) = p
参数：k + 1；hirr : Irreducible (cyclotomic (p ^ (k + 1)) K)；h : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two`：norm_sub_one_of_prime_ne_t
wo {k : Nat} (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) [hpri : Fact p.Prime] [IsCy
clotomicExtension {p ^ (k + 1)} K …
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n

--- 原说明 ---
If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p
` is an odd
prime, then the norm of `zeta (p ^ (k + 1)) K L - 1` is `p`.
-/
theorem norm_zeta_pow_sub_one_of_prime_ne_two {k : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K)) (h : p ≠ 2) :
    norm K (zeta (p ^ (k + 1)) K L - 1) = p :=
  (zeta_spec _ K L).norm_sub_one_of_prime_ne_two hirr h

/-- If `Irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `zeta p K L - 1` is `p`. -/
/-
**IsCyclotomicExtension.norm_zeta_sub_one_of_prime_ne_two** 是 Mathlib 中的一个定理，位于命
名空间 `IsCyclotomicExtension`。
形式化陈述：norm_zeta_sub_one_of_prime_ne_two [Fact p.Prime] [IsCyclotomicExtension {p
} K L] (hirr : Irreducible (cyclotomic p K)) (h : p != 2) : norm K (zeta p K L -
 1) = p
参数：hirr : Irreducible (cyclotomic p K)；h : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two'`：norm_sub_one_of_prime_ne_
two' [hpri : Fact p.Prime] [hcyc : IsCyclotomicExtension {p} K L] (hζ : IsPrimit
iveRoot ζ p) (hirr : Irreducible (c…
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n

--- 原说明 ---
If `Irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd 
prime,
then the norm of `zeta p K L - 1` is `p`.
-/
theorem norm_zeta_sub_one_of_prime_ne_two [Fact p.Prime]
    [IsCyclotomicExtension {p} K L] (hirr : Irreducible (cyclotomic p K)) (h : p ≠ 2) :
    norm K (zeta p K L - 1) = p :=
  (zeta_spec _ K L).norm_sub_one_of_prime_ne_two' hirr h

/-- If `Irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is at least `2`,
then the norm of `zeta (2 ^ k) K L - 1` is `2`. -/
/-
**IsCyclotomicExtension.norm_zeta_pow_sub_one_two** 是 Mathlib 中的一个定理，位于命名空间 `IsC
yclotomicExtension`。
形式化陈述：norm_zeta_pow_sub_one_two {k : Nat} (hk : 2 <= k) [IsCyclotomicExtension {
2 ^ k} K L] (hirr : Irreducible (cyclotomic (2 ^ k) K)) : norm K (zeta (2 ^ k) K
 L - 1) = 2
参数：hk : 2 <= k；hirr : Irreducible (cyclotomic (2 ^ k) K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.norm_sub_one_two`：norm_sub_one_two {k : Nat} (hζ : IsPri
mitiveRoot ζ (2 ^ k)) (hk : 2 <= k) [H : IsCyclotomicExtension {2 ^ k} K L] (hir
r : Irreducible (cyclo…
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n

--- 原说明 ---
If `Irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is a
t least `2`,
then the norm of `zeta (2 ^ k) K L - 1` is `2`.
-/
theorem norm_zeta_pow_sub_one_two {k : ℕ} (hk : 2 ≤ k)
    [IsCyclotomicExtension {2 ^ k} K L] (hirr : Irreducible (cyclotomic (2 ^ k) K)) :
    norm K (zeta (2 ^ k) K L - 1) = 2 :=
  norm_sub_one_two (zeta_spec (2 ^ k) K L) hk hirr

end IsCyclotomicExtension
end Norm

