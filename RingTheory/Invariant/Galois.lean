/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Invariant Extensions of Rings and Galois Theory

Given an extension of rings `B/A` and an action of `G` on `B`, the predicate
`Algebra.IsInvariant A B G` states that every fixed point of `B` lies in the image of `A`.

This file relates this predicate `Algebra.IsInvariant` to Galois theory.
-/

@[expose] public section

open scoped Pointwise

section Galois

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L]

/-- In the AKLB setup, the Galois group of `L/K` acts on `B`. -/
@[implicit_reducible]
/-
**IsIntegralClosure.MulSemiringAction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsIntegralClosure.MulSemiringAction [Algebra.IsAlgebraic K L] : MulSemirin
gAction Gal(L/K) B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the AKLB setup, the Galois group of `L/K` acts on `B`.
-/
noncomputable def IsIntegralClosure.MulSemiringAction [Algebra.IsAlgebraic K L] :
    MulSemiringAction Gal(L/K) B :=
  MulSemiringAction.compHom B (galRestrict A K L B).toMonoidHom
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsAlgebraic K L] : let := IsIntegralClosure.MulSemiringAction A K L B
    SMulDistribClass Gal(L/K) B L :=
  let := IsIntegralClosure.MulSemiringAction A K L B
  ⟨fun g b l ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    exact Or.inl (algebraMap_galRestrictHom_apply A K L B g b).symm⟩

/-- In the AKLB setup, every fixed point of `B` lies in the image of `A`. -/
/-
**Algebra.isInvariant_of_isGalois** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isInvariant_of_isGalois [FiniteDimensional K L] [h : IsGalois K L]
 : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsGalois.tfae`：tfae [FiniteDimensional F E] : List.TFAE [ IsGalois F E, 
IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) = ⊥, Nat.card Gal(E/F) = fi
nra…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `algebraMap_galRestrict_apply`：algebraMap_galRestrict_apply (σ : Gal(L/K)
) (x : B) : algebraMap B L (galRestrict A K L B σ x) = σ (algebraMap B L x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.mem_bot`：mem_bot {x : E} : x in (⊥ : IntermediateField
 F E) ↔ x in Set.range (algebraMap F E)
· 使用定理 `IsIntegralClosure.isIntegral`：∀ (R : Type u_1) {A : Type u_2} (B : Type 
u_3) [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : CommRing B]   [inst_3 :
 Algebra R B] [ins…
· 使用定理 `IsIntegrallyClosed.algebraMap_eq_of_integral`：algebraMap_eq_of_integral 
[IsIntegrallyClosed R] {x : K} : IsIntegral R x -> exists y : R, algebraMap R K 
y = x
· 使用定理 `isIntegral_algebraMap_iff`：isIntegral_algebraMap_iff [Algebra A B] [IsSc
alarTower R A B] {x : A} (hAB : Function.Injective (algebraMap A B)) : IsIntegra
l R (algebraMap…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)

--- 原说明 ---
In the AKLB setup, every fixed point of `B` lies in the image of `A`.
-/
theorem Algebra.isInvariant_of_isGalois [FiniteDimensional K L] [h : IsGalois K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    Algebra.IsInvariant A B Gal(L/K) := by
  replace h := ((IsGalois.tfae (F := K) (E := L)).out 0 1).mp h
  let := IsIntegralClosure.MulSemiringAction A K L B
  refine ⟨fun b hb ↦ ?_⟩
  replace hb : algebraMap B L b ∈ IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)) := by
    rintro ⟨g, -⟩
    exact (algebraMap_galRestrict_apply A g b).symm.trans (congrArg (algebraMap B L) (hb g))
  rw [h, IntermediateField.mem_bot] at hb
  obtain ⟨k, hk⟩ := hb
  have hb : IsIntegral A b := IsIntegralClosure.isIntegral A L b
  rw [← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective B L), ← hk,
    isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective K L)] at hb
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hb
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L,
    (FaithfulSMul.algebraMap_injective B L).eq_iff] at hk
  exact ⟨a, hk⟩

/-- A variant of `Algebra.isInvariant_of_isGalois`, replacing `Gal(L/K)` by `Aut(B/A)`. -/
/-
**Algebra.isInvariant_of_isGalois'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isInvariant_of_isGalois' [FiniteDimensional K L] [IsGalois K L] : 
Algebra.IsInvariant A B (B ≃ₐ[A] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsInvariant.isInvariant`：∀ {A : Type u_1} {B : Type u_2} {G : Ty
pe u_3} {inst : CommSemiring A} {inst_1 : Semiring B} {inst_2 : Algebra A B}   {
inst_3 : Group G} {in…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `Algebra.isInvariant_of_isGalois`：Algebra.isInvariant_of_isGalois [Finite
Dimensional K L] [h : IsGalois K L] : letI

--- 原说明 ---
A variant of `Algebra.isInvariant_of_isGalois`, replacing `Gal(L/K)` by `Aut(B/A
)`.
-/
theorem Algebra.isInvariant_of_isGalois' [FiniteDimensional K L] [IsGalois K L] :
    Algebra.IsInvariant A B (B ≃ₐ[A] B) :=
  ⟨fun b h ↦ (isInvariant_of_isGalois A K L B).1 b (fun g ↦ h (galRestrict A K L B g))⟩

end Galois

section normal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Finite G] [Group G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]

namespace Ideal.IsFractionRing

variable [P.IsPrime] [Q.IsPrime] (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K] [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
    [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L] [IsScalarTower (A ⧸ P) K L]

open Polynomial in
include P Q G in
/-
**Ideal.IsFractionRing.normal** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.IsFractionRing`。
形式化陈述：normal : Normal K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsInvariant.isIntegral`：isIntegral [Finite G] : Algebra.IsIntegr
al A B
· 使用引理 `isAlgebraic_of_isFractionRing`：isAlgebraic_of_isFractionRing (R S K L) [
CommRing R] [CommRing S] [Field K] [CommRing L] [Algebra R S] [Algebra R K] [Alg
ebra R L] [Algebra …
· 使用定理 `Ideal.Quotient.algebra_isIntegral_of_liesOver`：∀ {A : Type u_1} [inst : 
CommRing A] {B : Type u_2} [inst_1 : CommRing B] [inst_2 : Algebra A B]   [Algeb
ra.IsIntegral A B] (P : Ideal B) (p…
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `IsAlgebraic.exists_smul_eq_mul`：IsAlgebraic.exists_smul_eq_mul (a : S) {
b : S} (hRb : IsAlgebraic R b) (hb : b in S⁰) : existsᵉ (c : S) (d != (0 : R)), 
d • a = b * c
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Polynomial.lifts_and_natDegree_eq_and_monic`：lifts_and_natDegree_eq_and_
monic {p : S[X]} (hlifts : p in lifts f) (hp : p.Monic) : exists q : R[X], map f
 q = p ∧ q.natDegree = p.natDegre…
· 使用定理 `Algebra.IsInvariant.charpoly_mem_lifts`：charpoly_mem_lifts [Fintype G] (
b : B) : charpoly G b in Polynomial.lifts (algebraMap A B)
· 使用定理 `MulSemiringAction.monic_charpoly`：monic_charpoly (b : B) : (charpoly G b
).Monic
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `MulSemiringAction.eval_charpoly`：eval_charpoly (b : B) : (charpoly G b).
eval b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_comp`：map_comp (p q : R[X]) : map f (p.comp q) = (map f p
).comp (map f q)
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.aeval_comp`：aeval_comp {A : Type*} [Semiring A] [Algebra R A]
 (x : A) : aeval x (p.comp q) = aeval (aeval x q) p
· 使用定理 `Polynomial.aeval_mul`：aeval_mul : aeval x (p * q) = aeval x p * aeval x 
q
（共 62 条，此处仅展示前 30 条）
-/
lemma normal : Normal K L := by
  have := Algebra.IsInvariant.isIntegral A B G
  have := isAlgebraic_of_isFractionRing (A ⧸ P) (B ⧸ Q) K L
  constructor
  intro x
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (B ⧸ Q) x
  obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A ⧸ P) y).exists_smul_eq_mul x hy
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective b
  simp_rw [← Quotient.algebraMap_eq] at *
  cases nonempty_fintype G
  obtain ⟨p, hp, -, h_monic⟩ := lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts A B G b) (MulSemiringAction.monic_charpoly ..)
  have h_eval : p.aeval b = 0 := by
    rw [← eval_map_algebraMap, hp, MulSemiringAction.eval_charpoly]
  let q := p.comp (C a * X)
  let d := (algebraMap (B ⧸ Q) L) x / (algebraMap (B ⧸ Q) L) y
  have comm₁ : (algebraMap K L).comp (algebraMap (A ⧸ P) K) =
      (algebraMap (B ⧸ Q) L).comp (algebraMap (A ⧸ P) (B ⧸ Q)) := by
    simp_rw [← IsScalarTower.algebraMap_eq]
  have comm₂ : (algebraMap (A ⧸ P) (B ⧸ Q)).comp (algebraMap A (A ⧸ P)) =
      (algebraMap B (B ⧸ Q)).comp (algebraMap A B) := by
    simp_rw [← IsScalarTower.algebraMap_eq]
  replace h_eval : ((q.map (algebraMap A (A ⧸ P))).map (algebraMap (A ⧸ P) K)).aeval d = 0 := by
    simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, aeval_comp, aeval_mul, aeval_C, aeval_X,
      ← RingHom.comp_apply, ← RingHom.comp_assoc, comm₁, RingHom.comp_apply, d, mul_div, ← map_mul]
    rw [← Algebra.smul_def, h, map_mul, mul_div_cancel_left₀ _ (by simpa using hy),
      aeval_map_algebraMap, aeval_algebraMap_apply, aeval_map_algebraMap, aeval_algebraMap_apply,
      h_eval, map_zero, map_zero]
  replace h_splits : (p.map (algebraMap A B)).Splits := by
    rw [hp]
    exact MulSemiringAction.splits_charpoly G b
  refine .of_dvd ?_ ?_ (map_dvd (algebraMap K L) (minpoly.dvd K d h_eval))
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X]
    refine .comp_of_degree_le_one ?_ (degree_C_mul_X_le _)
    rw [Polynomial.map_map, Polynomial.map_map, comm₁, RingHom.comp_assoc, comm₂,
      ← RingHom.comp_assoc, ← Polynomial.map_map]
    apply h_splits.map
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, Polynomial.map_map]
    exact mt (comp_C_mul_X_eq_zero_iff (by simpa)).mp (map_monic_ne_zero h_monic)

include P Q in
/-
**Ideal.IsFractionRing.finite_of_isInvariant** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Is
FractionRing`。
形式化陈述：finite_of_isInvariant [SMulCommClass G A B] [Algebra.IsSeparable K L] : Mo
dule.Finite K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.IsFractionRing.normal`：normal : Normal K L
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `IsFractionRing.stabilizerHom_surjective`：IsFractionRing.stabilizerHom_su
rjective : Function.Surjective (stabilizerHom G P Q K L)
· 使用引理 `IsGalois.finiteDimensional_of_finite`：finiteDimensional_of_finite [IsGal
ois F E] [Finite Gal(E/F)] : FiniteDimensional F E
-/
lemma finite_of_isInvariant [SMulCommClass G A B] [Algebra.IsSeparable K L] :
    Module.Finite K L := by
  have : IsGalois K L := { __ := normal G P Q K L }
  have := Finite.of_surjective _ (IsFractionRing.stabilizerHom_surjective G P Q K L)
  apply IsGalois.finiteDimensional_of_finite

end Ideal.IsFractionRing

attribute [local instance] Ideal.Quotient.field in
include G in
/--
For any domain `k` containing `B ⧸ Q`,
any endomorphism of `k` can be restricted to an endomorphism of `B ⧸ Q`. -/
/-
**Ideal.Quotient.normal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.Quotient.normal [P.IsMaximal] [Q.IsMaximal] : Normal (A ⧸ P) (B ⧸ Q)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.IsFractionRing.normal`：normal : Normal K L
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `instIsFractionRing`：∀ {R : Type u_6} [inst : Field R], IsFractionRing R 
R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
For any domain `k` containing `B ⧸ Q`,
any endomorphism of `k` can be restricted to an endomorphism of `B ⧸ Q`.
-/
lemma Ideal.Quotient.normal [P.IsMaximal] [Q.IsMaximal] :
    Normal (A ⧸ P) (B ⧸ Q) :=
  IsFractionRing.normal G P Q (A ⧸ P) (B ⧸ Q)

attribute [local instance] Ideal.Quotient.field in
include G in
/-- If the extension `B/Q` over `A/P` is separable, then it is finite dimensional. -/
/-
**Ideal.Quotient.finite_of_isInvariant** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.Quotient.finite_of_isInvariant [P.IsMaximal] [Q.IsMaximal] [SMulComm
Class G A B] [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)] : Module.Finite (A ⧸ P) (B ⧸ 
Q)
参数：A ⧸ P；B ⧸ Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.IsFractionRing.finite_of_isInvariant`：finite_of_isInvariant [SMulC
ommClass G A B] [Algebra.IsSeparable K L] : Module.Finite K L
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `instIsFractionRing`：∀ {R : Type u_6} [inst : Field R], IsFractionRing R 
R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
If the extension `B/Q` over `A/P` is separable, then it is finite dimensional.
-/
lemma Ideal.Quotient.finite_of_isInvariant [P.IsMaximal] [Q.IsMaximal]
    [SMulCommClass G A B] [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)] :
    Module.Finite (A ⧸ P) (B ⧸ Q) :=
  IsFractionRing.finite_of_isInvariant G P Q (A ⧸ P) (B ⧸ Q)

end normal

