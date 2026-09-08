/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.RingHom.Flat

/-!

# Results for the rank of a finite flat algebra

In this file we study a finite, flat `R`-algebra `S` and relate injectivity and
bijectivity of `R → S` with the rank of `S` over `R`.

## Main results

- `PrimeSpectrum.comap_surjective_iff_injective_of_finite`: `Spec S → Spec R` is surjective
  if and only if `R → S` is injective.
- `Module.Flat.tfae_algebraMap_surjective`: `R → S` is surjective iff `S ⊗[R] S → S` is an
  isomorphism iff the rank of `S` is at most `1` at all primes.
- `Module.algebraMap_bijective_iff_rankAtStalk`: `S` is of constant `R`-rank `1` if and only if
  `S` is isomorphic to `R`.

-/

public section

universe u

open TensorProduct

attribute [local instance] Module.free_of_flat_of_isLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

section

variable [Module.Flat R S] [Module.Finite R S]

/-
**PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap (p : PrimeSpectrum R) : 
0 < Module.rankAtStalk (R
参数：p : PrimeSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.rankAtStalk_eq`：rankAtStalk_eq (p : PrimeSpectrum R) : rankAtStal
k M p = finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M)
· 使用定理 `Module.finrank_pos_iff`：Module.finrank_pos_iff [IsDomain R] [IsTorsionFr
ee R M] : 0 < finrank R M ↔ Nontrivial M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `PrimeSpectrum.nontrivial_iff_mem_rangeComap`：PrimeSpectrum.nontrivial_if
f_mem_rangeComap {S : Type*} [CommRing S] [Algebra R S] (p : PrimeSpectrum R) : 
Nontrivial (p.asIdeal.ResidueFiel…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap (p : PrimeSpectrum R) :
    0 < Module.rankAtStalk (R := R) S p ↔ p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
  rw [Module.rankAtStalk_eq, Module.finrank_pos_iff, p.nontrivial_iff_mem_rangeComap]

/-- The rank is positive at all stalks if and only if the induced map on prime spectra is
surjective. -/
/-
**PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective : (forall p, 0 < Module
.rankAtStalk (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The rank is positive at all stalks if and only if the induced map on prime spect
ra is
surjective.
-/
lemma PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective :
    (∀ p, 0 < Module.rankAtStalk (R := R) S p) ↔
      Function.Surjective (PrimeSpectrum.comap <| algebraMap R S) := by
  simp_rw [rankAtStalk_pos_iff_mem_range_comap, ← Set.range_eq_univ,
    Set.eq_univ_iff_forall]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-
**PrimeSpectrum.comap_surjective_iff_injective_of_finite** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：PrimeSpectrum.comap_surjective_iff_injective_of_finite : (PrimeSpectrum.co
map (algebraMap R S)).Surjective ↔ Function.Injective (algebraMap R S)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `injective_of_isLocalization_isMaximal`：injective_of_isLocalization_isMax
imal (H : forall (p : Ideal R) [p.IsMaximal], Function.Injective (algebraMap (Rₚ
 p) (Sₚ p))) : Function.Inj…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `OreLocalization.instSMulCommClass`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `instIsLocalizedModuleTensorProductSemilinearMapAlgHomToAlgHom`：∀ {R : Ty
pe u_1} [inst : CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommS
emiring A]   [inst_2 : Algebra R A] [IsLocalization…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.IsIntegral.comap_surjective`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.IsInteg
ral R S] [FaithfulSMul R …
-/
lemma PrimeSpectrum.comap_surjective_iff_injective_of_finite :
    (PrimeSpectrum.comap (algebraMap R S)).Surjective ↔ Function.Injective (algebraMap R S) := by
  refine ⟨fun h ↦ ?_, fun h ↦
    have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr h
    Algebra.IsIntegral.comap_surjective _ _⟩
  apply injective_of_isLocalization_isMaximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Localization.AtPrime P ⊗[R] S)
  intro p _
  rw [← faithfulSMul_iff_algebraMap_injective]
  obtain ⟨⟨Q, _⟩, hQ⟩ := h ⟨p, inferInstance⟩
  have : Q.LiesOver p := ⟨congr($(hQ).asIdeal).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : Nontrivial (Localization.AtPrime p ⊗[R] S) := by
    let f : Localization.AtPrime p ⊗[R] S →ₐ[R] Localization.AtPrime Q :=
      Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R _ _)
        (IsScalarTower.toAlgHom R S _) (fun _ _ ↦ Commute.all _ _)
    exact f.domain_nontrivial
  infer_instance
/-
**Module.rankAtStalk_pos_iff_algebraMap_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.rankAtStalk_pos_iff_algebraMap_injective : (forall p, 0 < Module.ra
nkAtStalk (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PrimeSpectrum.comap_surjective_iff_injective_of_finite`：PrimeSpectrum.co
map_surjective_iff_injective_of_finite : (PrimeSpectrum.comap (algebraMap R S)).
Surjective ↔ Function.Injective (algebraMap …
· 使用引理 `PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective`：PrimeSpectrum.rankAt
Stalk_pos_iff_comap_surjective : (forall p, 0 < Module.rankAtStalk (R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Module.rankAtStalk_pos_iff_algebraMap_injective :
    (∀ p, 0 < Module.rankAtStalk (R := R) S p) ↔ Function.Injective (algebraMap R S) := by
  rw [← PrimeSpectrum.comap_surjective_iff_injective_of_finite,
    PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-
**Module.algebraMap_surjective_of_rankAtStalk_le_one** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：Module.algebraMap_surjective_of_rankAtStalk_le_one (h : forall p, rankAtSt
alk (R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `surjective_of_isLocalization_isMaximal`：surjective_of_isLocalization_isM
aximal (H : forall (p : Ideal R) [p.IsMaximal], Function.Surjective (algebraMap 
(Rₚ p) (Sₚ p))) : Function.S…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `OreLocalization.instSMulCommClass`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `instIsLocalizedModuleTensorProductSemilinearMapAlgHomToAlgHom`：∀ {R : Ty
pe u_1} [inst : CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommS
emiring A]   [inst_2 : Algebra R A] [IsLocalization…
· 使用引理 `Module.subsingleton_of_rank_zero`：subsingleton_of_rank_zero (h : Module.
rank R M = 0) : Subsingleton M
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.rankAtStalk_eq_finrank_tensorProduct`：rankAtStalk_eq_finrank_tens
orProduct (p : PrimeSpectrum R) : rankAtStalk M p = finrank (Localization.AtPrim
e p.asIdeal) (Localization.AtPrim…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.surjective_to_subsingleton`：surjective_to_subsingleton [na : No
nempty α] [Subsingleton β] (f : α -> β) : Surjective f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Module.Free.bijective_algebraMap_of_finrank_eq_one`：Module.Free.bijectiv
e_algebraMap_of_finrank_eq_one {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
 [Nontrivial R] [Free R S] (h : finrank …
-/
lemma Module.algebraMap_surjective_of_rankAtStalk_le_one (h : ∀ p, rankAtStalk (R := R) S p ≤ 1) :
    Function.Surjective (algebraMap R S) := by
  apply surjective_of_isLocalization_isMaximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Localization.AtPrime P ⊗[R] S)
  intro p _
  by_cases hr : Module.rankAtStalk S ⟨p, inferInstance⟩ = 0
  · have : Subsingleton (Localization.AtPrime p ⊗[R] S) := by
      apply Module.subsingleton_of_rank_zero (R := Localization.AtPrime p)
      simp [← finrank_eq_rank, ← rankAtStalk_eq_finrank_tensorProduct ⟨p, inferInstance⟩, hr]
    exact Function.surjective_to_subsingleton _
  · refine (Free.bijective_algebraMap_of_finrank_eq_one ?_).2
    grind [rankAtStalk_eq_finrank_tensorProduct ⟨p, inferInstance⟩]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
variable (R) (S) in
/-- If `S` is a finite and flat `R`-algebra, `R → S` is surjective iff `S ⊗[R] S → S` is an
isomorphism iff the rank of `S` is at most `1` at all primes. -/
/-
**Module.Flat.tfae_algebraMap_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.Flat.tfae_algebraMap_surjective : [Function.Surjective (algebraMap 
R S), Function.Bijective (LinearMap.mul' R S), (forall p, Module.rankAtStalk (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.mul'_bijective_of_surjective`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A],   Func
tion.Surjective ⇑(algebraMap…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Module.rankAtStalk_tensorProduct`：rankAtStalk_tensorProduct (N : Type*) 
[AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Flat R N] : rankAtStal
k (M otimes[R] N) = ra…
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.succ_succ_ne_one`：∀ (a : ℕ), a.succ.succ ≠ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.pow_eq_self_iff`：∀ {a b : ℕ}, 1 < a → (a ^ b = a ↔ b = 1)
· 使用引理 `Module.rankAtStalk_eq_of_equiv`：rankAtStalk_eq_of_equiv {N : Type*} [Add
CommGroup N] [Module R N] (e : M ≃ₗ[R] N) : rankAtStalk (R
· 使用引理 `Module.algebraMap_surjective_of_rankAtStalk_le_one`：Module.algebraMap_su
rjective_of_rankAtStalk_le_one (h : forall p, rankAtStalk (R
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)

--- 原说明 ---
If `S` is a finite and flat `R`-algebra, `R → S` is surjective iff `S ⊗[R] S → S
` is an
isomorphism iff the rank of `S` is at most `1` at all primes.
-/
lemma Module.Flat.tfae_algebraMap_surjective :
    [Function.Surjective (algebraMap R S),
      Function.Bijective (LinearMap.mul' R S),
      (∀ p, Module.rankAtStalk (R := R) S p ≤ 1)].TFAE := by
  tfae_have 1 → 2 := LinearMap.mul'_bijective_of_surjective _ _
  tfae_have 2 → 3 := fun H p ↦ by
    have h : rankAtStalk (S ⊗[R] S) p = rankAtStalk S p ^ 2 := by
      simp [rankAtStalk_tensorProduct, sq]
    by_contra! hc
    apply Nat.succ_succ_ne_one 0
    rw [← Nat.pow_eq_self_iff hc, ← h, Module.rankAtStalk_eq_of_equiv
      (AlgEquiv.ofBijective (Algebra.TensorProduct.lmul' R (S := S)) H).toLinearEquiv]
  tfae_have 3 → 1 := Module.algebraMap_surjective_of_rankAtStalk_le_one
  tfae_finish
/-
**Module.rankAtStalk_le_one_iff_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.rankAtStalk_le_one_iff_surjective : (forall p, Module.rankAtStalk (
R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Module.Flat.tfae_algebraMap_surjective`：Module.Flat.tfae_algebraMap_surj
ective : [Function.Surjective (algebraMap R S), Function.Bijective (LinearMap.mu
l' R S), (forall p, Module.r…
-/
lemma Module.rankAtStalk_le_one_iff_surjective :
    (∀ p, Module.rankAtStalk (R := R) S p ≤ 1) ↔ Function.Surjective (algebraMap R S) :=
  (Module.Flat.tfae_algebraMap_surjective R S).out 2 0

/-- If `S` is a finite, flat `R`-algebra, `S` is of constant rank `1` if and only if
`S` is isomorphic to `R`. -/
/-
**Module.algebraMap_bijective_iff_rankAtStalk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.algebraMap_bijective_iff_rankAtStalk : Module.rankAtStalk (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Bijective.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} (f : α → β), Func
tion.Bijective f = (Function.Injective f ∧ Function.Surjective f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.rankAtStalk_pos_iff_algebraMap_injective`：Module.rankAtStalk_pos_
iff_algebraMap_injective : (forall p, 0 < Module.rankAtStalk (R
· 使用引理 `Module.rankAtStalk_le_one_iff_surjective`：Module.rankAtStalk_le_one_iff_
surjective : (forall p, Module.rankAtStalk (R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1

--- 原说明 ---
If `S` is a finite, flat `R`-algebra, `S` is of constant rank `1` if and only if
`S` is isomorphic to `R`.
-/
lemma Module.algebraMap_bijective_iff_rankAtStalk :
    Module.rankAtStalk (R := R) S = 1 ↔ Function.Bijective (algebraMap R S) := by
  rw [Function.Bijective, ← rankAtStalk_pos_iff_algebraMap_injective,
    ← rankAtStalk_le_one_iff_surjective]
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  ext p
  rw [Pi.one_apply]
  grind

alias ⟨Module.algebraMap_bijective_of_rankAtStalk, _⟩ := Module.algebraMap_bijective_iff_rankAtStalk

end

section

/-- The rank of a ring homomorphism `f : R →+* S` at a prime `x` of `R` is the rank of
`S` as an `R`-module at the stalk of `x`. -/
@[expose]
/-
**RingHom.finrank** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.finrank {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) (x 
: PrimeSpectrum R) : Nat
参数：f : R ->+* S；x : PrimeSpectrum R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank of a ring homomorphism `f : R →+* S` at a prime `x` of `R` is the rank 
of
`S` as an `R`-module at the stalk of `x`.
-/
noncomputable def RingHom.finrank {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : PrimeSpectrum R) : ℕ :=
  letI : Algebra R S := f.toAlgebra
  Module.rankAtStalk S x

@[simp]
/-
**RingHom.finrank_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.finrank_algebraMap : (algebraMap R S).finrank = Module.rankAtStalk
 (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.finrank.eq_1`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing R
] [inst_1 : CommRing S] (f : R →+* S) (x : PrimeSpectrum R),   f.finrank x = Mod
ule.rankAt…
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
-/
lemma RingHom.finrank_algebraMap :
    (algebraMap R S).finrank = Module.rankAtStalk (R := R) S := by
  ext
  rw [RingHom.finrank, toAlgebra_algebraMap]
/-
**Algebra.rankAtStalk_eq_of_isPushout** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.rankAtStalk_eq_of_isPushout (R S : Type*) [CommRing R] [CommRing S
] [Algebra R S] (R' S' : Type*) [CommRing R'] [CommRing S'] [Algebra R R'] [Alge
bra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower 
R S S'] [Algebra.IsPushout R S R' S'] [Module.Flat R S] [Module.Finite R S] (x :
 PrimeSpectrum R') : Module.rankAtStalk S' x = Module.rankAtStalk S (PrimeSpectr
um.comap (algebraMap R R') x)
参数：R S : Type*；R' S' : Type*；x : PrimeSpectrum R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsPushout.symm`：Algebra.IsPushout.symm (h : Algebra.IsPushout R 
S R' S') : Algebra.IsPushout R R' S S' where out
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Module.rankAtStalk_eq_of_equiv`：rankAtStalk_eq_of_equiv {N : Type*} [Add
CommGroup N] [Module R N] (e : M ≃ₗ[R] N) : rankAtStalk (R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.rankAtStalk_baseChange`：rankAtStalk_baseChange {S : Type*} [CommR
ing S] [Algebra R S] (p : PrimeSpectrum S) : rankAtStalk (S otimes[R] M) p = ran
kAtStalk M (p.comap…
-/
lemma Algebra.rankAtStalk_eq_of_isPushout (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (R' S' : Type*) [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R S R' S'] [Module.Flat R S] [Module.Finite R S] (x : PrimeSpectrum R') :
    Module.rankAtStalk S' x = Module.rankAtStalk S (PrimeSpectrum.comap (algebraMap R R') x) := by
  have : IsPushout R R' S S' := Algebra.IsPushout.symm inferInstance
  have := Module.rankAtStalk_eq_of_equiv (Algebra.IsPushout.equiv R R' S S').symm.toLinearEquiv
  rw [Module.rankAtStalk_eq_of_equiv (Algebra.IsPushout.equiv R R' S S').symm.toLinearEquiv,
    Module.rankAtStalk_baseChange]
/-
**RingHom.finrank_comp_left_of_bijective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.finrank_comp_left_of_bijective {R S T : Type*} [CommRing R] [CommR
ing S] [CommRing T] (f : R ->+* S) (g : S ->+* T) (hf : Function.Bijective g) (h
1 : f.Finite) (h2 : f.Flat) (x : PrimeSpectrum R) : (g.comp f).finrank x = f.fin
rank x
参数：f : R ->+* S；g : S ->+* T；hf : Function.Bijective g；h1 : f.Finite；h2 : f.Flat
；x : PrimeSpectrum R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用引理 `Algebra.IsPushout.of_bijective_right`：Algebra.IsPushout.of_bijective_rig
ht [Algebra A T] [IsScalarTower R A T] (H : Function.Bijective (algebraMap A T))
 : IsPushout R A R T
· 使用引理 `Algebra.rankAtStalk_eq_of_isPushout`：Algebra.rankAtStalk_eq_of_isPushout
 (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (R' S' : Type*) [CommRing
 R'] [CommRing S'] [Algeb…
-/
lemma RingHom.finrank_comp_left_of_bijective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hf : Function.Bijective g) (h1 : f.Finite) (h2 : f.Flat)
    (x : PrimeSpectrum R) : (g.comp f).finrank x = f.finrank x := by
  algebraize [f, g, (g.comp f)]
  have : Algebra.IsPushout R S R T := .of_bijective_right _ _ hf
  apply Algebra.rankAtStalk_eq_of_isPushout

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-
**RingHom.finrank_comp_right_of_bijective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.finrank_comp_right_of_bijective {R S T : Type*} [CommRing R] [Comm
Ring S] [CommRing T] (f : R ->+* S) (g : S ->+* T) (hg : Function.Bijective f) (
h1 : g.Finite) (h2 : g.Flat) (y : PrimeSpectrum R) (x : PrimeSpectrum S) (hy : y
 = PrimeSpectrum.comap f x) : (g.comp f).finrank y = g.finrank x
参数：f : R ->+* S；g : S ->+* T；hg : Function.Bijective f；h1 : g.Finite；h2 : g.Flat
；y : PrimeSpectrum R；x : PrimeSpectrum S；hy : y = PrimeSpectrum.comap f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `RingHom.Finite.comp`：comp {g : B ->+* C} {f : A ->+* B} (hg : g.Finite) 
(hf : f.Finite) : (g.comp f).Finite
· 使用定理 `RingHom.Finite.of_surjective`：of_surjective (f : A ->+* B) (hf : Surject
ive f) : f.Finite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `RingHom.Flat.comp`：comp {f : R ->+* S} {g : S ->+* T} (hf : f.Flat) (hg 
: g.Flat) : Flat (g.comp f)
· 使用引理 `RingHom.Flat.of_bijective`：of_bijective {f : R ->+* S} (hf : Function.Bi
jective f) : Flat f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Algebra.IsPushout.of_bijective_left`：Algebra.IsPushout.of_bijective_left
 [Algebra A T] [IsScalarTower R A T] (H : Function.Bijective (algebraMap R A)) :
 IsPushout R T A T
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.rankAtStalk_eq_of_isPushout`：Algebra.rankAtStalk_eq_of_isPushout
 (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (R' S' : Type*) [CommRing
 R'] [CommRing S'] [Algeb…
-/
lemma RingHom.finrank_comp_right_of_bijective {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (f : R →+* S) (g : S →+* T) (hg : Function.Bijective f) (h1 : g.Finite)
    (h2 : g.Flat) (y : PrimeSpectrum R) (x : PrimeSpectrum S)
    (hy : y = PrimeSpectrum.comap f x) :
    (g.comp f).finrank y = g.finrank x := by
  subst hy
  algebraize [f, g, (g.comp f)]
  have : Module.Finite R T := h1.comp <| .of_surjective _ hg.2
  have : Module.Flat R T := (RingHom.Flat.of_bijective hg).comp h2
  have : Algebra.IsPushout R T S T := .of_bijective_left _ _ hg
  exact (Algebra.rankAtStalk_eq_of_isPushout _ _ _ _ _).symm
/-
**CommRingCat.finrank_eq_of_isPushout** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CommRingCat.finrank_eq_of_isPushout {R S T P : CommRingCat.{u}} {f : R ⟶ S
} {g : R ⟶ T} {inl : S ⟶ P} {inr : T ⟶ P} (h : CategoryTheory.IsPushout f g inl 
inr) (hf : f.hom.Flat) (hfin : f.hom.Finite) (x : PrimeSpectrum T) : inr.hom.fin
rank x = f.hom.finrank (PrimeSpectrum.comap g.hom x)
参数：h : CategoryTheory.IsPushout f g inl inr；hf : f.hom.Flat；hfin : f.hom.Finite；
x : PrimeSpectrum T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CommRingCat.isPushout_iff_isPushout`：isPushout_iff_isPushout {R S : Type
 u} [CommRing R] [CommRing S] [Algebra R S] {R' S' : Type u} [CommRing R'] [Comm
Ring S'] [Algebra R R'] […
· 使用引理 `Algebra.rankAtStalk_eq_of_isPushout`：Algebra.rankAtStalk_eq_of_isPushout
 (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (R' S' : Type*) [CommRing
 R'] [CommRing S'] [Algeb…
-/
lemma CommRingCat.finrank_eq_of_isPushout {R S T P : CommRingCat.{u}} {f : R ⟶ S} {g : R ⟶ T}
    {inl : S ⟶ P} {inr : T ⟶ P} (h : CategoryTheory.IsPushout f g inl inr) (hf : f.hom.Flat)
    (hfin : f.hom.Finite) (x : PrimeSpectrum T) :
    inr.hom.finrank x = f.hom.finrank (PrimeSpectrum.comap g.hom x) := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
  have : IsScalarTower R T P := .of_algebraMap_eq' <| congr($(h.1.1).hom)
  have : Algebra.IsPushout R S T P := CommRingCat.isPushout_iff_isPushout.mp h
  exact Algebra.rankAtStalk_eq_of_isPushout R S T P x

end

