/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.IsGaloisGroup.Basic

/-!
# Galois Groups of Fields

Given an action of a group `G` on an extension of fields `L/K`, the predicate `IsGaloisGroup G K L`
states that `G` acts faithfully on `L` with fixed field `K`. In particular, we do not assume that
`L` is an algebraic extension of `K`.

## Implementation notes

We actually define `IsGaloisGroup G A B` for extensions of rings `B/A`, with the same definition
(faithful action on `B` with fixed ring `A`). This definition turns out to axiomatize a common
setup in algebraic number theory where a Galois group `Gal(L/K)` acts on an extension of subrings
`B/A` (e.g., rings of integers). In particular, there are theorems in algebraic number theory that
naturally assume `[IsGaloisGroup G A B]` and whose statements would otherwise require assuming
`(K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L]` (along with predicates relating
`K` and `L` to the rings `A` and `B`) despite `K` and `L` not appearing in the conclusion.

Unfortunately, this definition of `IsGaloisGroup G A B` for extensions of rings `B/A` is
nonstandard and clashes with other notions such as the étale fundamental group. In particular, if
`G` is finite and `A` is integrally closed, then  `IsGaloisGroup G A B` is equivalent to `B/A`
being integral and the fields of fractions `Frac(B)/Frac(A)` being Galois with Galois group `G`
(see `IsGaloisGroup.iff_isFractionRing`), rather than `B/A` being étale for instance.

But in the absence of a more suitable name, the utility of the predicate `IsGaloisGroup G A B` for
extensions of rings `B/A` seems to outweigh these terminological issues.
-/

@[expose] public section

open Module

section Field

open NumberField

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (G : Type*) [Group G] [MulSemiringAction G L] [IsGaloisGroup G K L] :
    IsGaloisGroup G (𝓞 K) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing G (𝓞 K) (𝓞 L) K L
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : Type*) [Field L] [NumberField L]
    (G : Type*) [Group G] [MulSemiringAction G L] [IsGaloisGroup G ℚ L] :
    IsGaloisGroup G ℤ (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing G ℤ (𝓞 L) ℚ L

end Field

variable (G G' K L : Type*) [Group G] [Group G'] [Field K] [Field L] [Algebra K L]
  [MulSemiringAction G L] [MulSemiringAction G' L]

namespace IsGaloisGroup

attribute [instance low] commutes isInvariant

/-
**IsGaloisGroup.fixedPoints_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：fixedPoints_eq_bot [IsGaloisGroup G K L] : FixedPoints.intermediateField G
 = (⊥ : IntermediateField K L)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Algebra.IsInvariant.isInvariant`：∀ {A : Type u_1} {B : Type u_2} {G : Ty
pe u_3} {inst : CommSemiring A} {inst_1 : Semiring B} {inst_2 : Algebra A B}   {
inst_3 : Group G} {in…
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
-/
theorem fixedPoints_eq_bot [IsGaloisGroup G K L] :
    FixedPoints.intermediateField G = (⊥ : IntermediateField K L) := by
  rw [eq_bot_iff]
  exact Algebra.IsInvariant.isInvariant

/-- If `G` is a finite Galois group for `L/K`, then `L/K` is a Galois extension. -/
/-
**IsGaloisGroup.isGalois** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：isGalois [Finite G] [IsGaloisGroup G K L] : IsGalois K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isGalois_iff_isGalois_bot`：isGalois_iff_isGalois_bot : IsGalois (⊥ : Int
ermediateField F E) E ↔ IsGalois F E
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `IsGaloisGroup.fixedPoints_eq_bot`：fixedPoints_eq_bot [IsGaloisGroup G K 
L] : FixedPoints.intermediateField G = (⊥ : IntermediateField K L)

--- 原说明 ---
If `G` is a finite Galois group for `L/K`, then `L/K` is a Galois extension.
-/
theorem isGalois [Finite G] [IsGaloisGroup G K L] : IsGalois K L := by
  rw [← isGalois_iff_isGalois_bot, ← fixedPoints_eq_bot G]
  exact IsGalois.of_fixed_field L G

/-- If `L/K` is a Galois extension, then `Gal(L/K)` is a Galois group for `L/K`. -/
/-
**IsGaloisGroup.of_isGalois** 是 Mathlib 中的一个实例，位于命名空间 `IsGaloisGroup`。
形式化陈述：of_isGalois [IsGalois K L] : IsGaloisGroup Gal(L/K) K L where faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `InfiniteGalois.mem_bot_iff_fixed`：mem_bot_iff_fixed [IsGalois k K] (x : 
K) : x in (⊥ : IntermediateField k K) ↔ forall (f : Gal(K/k)), f x = x

--- 原说明 ---
If `L/K` is a Galois extension, then `Gal(L/K)` is a Galois group for `L/K`.
-/
instance of_isGalois [IsGalois K L] : IsGaloisGroup Gal(L/K) K L where
  faithful := inferInstance
  commutes := inferInstance
  isInvariant := ⟨fun x ↦ (InfiniteGalois.mem_bot_iff_fixed x).mpr⟩

/-- The cardinality of a Galois group equals the degree of the field extension.

See `IsGaloisGroup.card_eq_finrank'` for a ring-theoretic generalization assuming finiteness. -/
/-
**IsGaloisGroup.card_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：card_eq_finrank [IsGaloisGroup G K L] : Nat.card G = Module.finrank K L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.faithful`：∀ {G : Type u_1} (A : Type u_2) {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.finrank_bot'`：finrank_bot' : finrank (⊥ : Intermediate
Field F E) E = finrank F E
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `IsGaloisGroup.fixedPoints_eq_bot`：fixedPoints_eq_bot [IsGaloisGroup G K 
L] : FixedPoints.intermediateField G = (⊥ : IntermediateField K L)
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `FixedPoints.finrank_eq_card`：finrank_eq_card [Fintype G] [FaithfulSMul G
 F] : finrank (FixedPoints.subfield G F) F = Fintype.card G
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FiniteDimensional.of_finrank_pos`：of_finrank_pos (h : 0 < finrank K V) :
 FiniteDimensional K V
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x

--- 原说明 ---
The cardinality of a Galois group equals the degree of the field extension.

See `IsGaloisGroup.card_eq_finrank'` for a ring-theoretic generalization assumin
g finiteness.
-/
theorem card_eq_finrank [IsGaloisGroup G K L] : Nat.card G = Module.finrank K L := by
  rcases fintypeOrInfinite G with _ | hG
  · have : FaithfulSMul G L := faithful K
    rw [← IntermediateField.finrank_bot', ← fixedPoints_eq_bot G, Nat.card_eq_fintype_card]
    exact (FixedPoints.finrank_eq_card G L).symm
  · rw [Nat.card_eq_zero_of_infinite, eq_comm]
    contrapose! hG
    have : FiniteDimensional K L := FiniteDimensional.of_finrank_pos (Nat.zero_lt_of_ne_zero hG)
    exact Finite.of_injective (MulSemiringAction.toAlgAut G K L)
      (fun _ _ ↦ (faithful K).eq_of_smul_eq_smul ∘ DFunLike.ext_iff.mp)
/-
**IsGaloisGroup.finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：finiteDimensional [Finite G] [IsGaloisGroup G K L] : FiniteDimensional K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_finrank_pos`：of_finrank_pos (h : 0 < finrank K V) :
 FiniteDimensional K V
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `IsGaloisGroup.card_eq_finrank`：card_eq_finrank [IsGaloisGroup G K L] : N
at.card G = Module.finrank K L
-/
theorem finiteDimensional [Finite G] [IsGaloisGroup G K L] : FiniteDimensional K L :=
  FiniteDimensional.of_finrank_pos (card_eq_finrank G K L ▸ Nat.card_pos)
/-
**IsGaloisGroup.finite** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：∀ (G : Type u_1) [inst : Group G] (R : Type u_5) (B : Type u_6) [inst_1 : 
CommRing R] [inst_2 : CommRing B]   [inst_3 : Algebra R B] [Module.Finite R B] [
IsDomain B] [inst_6 : MulSemiringAction G B] [IsGaloisGroup G R B],   Finite G
参数：G : Type u_1；R : Type u_5；B : Type u_6。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Subring.instIsDomainSubtypeMem`：∀ {R : Type u_1} [inst : Ring R] [IsDoma
in R] (s : Subring R), IsDomain ↥s
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Subsemiring.instFaithfulSMulSubtypeMem`：∀ {M' : Type u_5} {α : Type u_6}
 [inst : SMul M' α] {S' : Type u_7} [inst_1 : SetLike S' M'] (s : S')   [Faithfu
lSMul M' α], FaithfulSMul (↥…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Subring.instNontrivialSubtypeMem`：∀ {R : Type u_1} [inst : NonAssocRing 
R] [Nontrivial R] (s : Subring R), Nontrivial ↥s
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Module.Finite.of_restrictScalars_finite`：of_restrictScalars_finite (R A 
M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M] [Module R M] [Module A M]
 [SMul R A] [IsScalarTower R …
· 使用定理 `IsGaloisGroup.to_isFractionRing_of_isIntegral`：IsGaloisGroup.to_isFracti
onRing_of_isIntegral [Algebra.IsIntegral A B] [hGAB : IsGaloisGroup G A B] : IsG
aloisGroup G K L where faithful
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `instIsGaloisGroupSubtypeMemSubringRangeAlgebraMap`：∀ (G : Type u_1) (A :
 Type u_2) (B : Type u_3) [inst : Group G] [inst_1 : CommRing A] [inst_2 : CommR
ing B]   [inst_3 : MulSemiringAction G …
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGaloisGroup.card_eq_finrank`：card_eq_finrank [IsGaloisGroup G K L] : N
at.card G = Module.finrank K L
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `instFiniteDimensionalFractionRingOfFinite`：∀ {R : Type u_1} {S : Type u_
2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [inst_3 : Is
Domain R]   [inst_4 : IsDomain …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Subring.instNoZeroDivisorsSubtypeMem`：∀ {R : Type u_1} [inst : NonAssocR
ing R] [NoZeroDivisors R] (s : Subring R), NoZeroDivisors ↥s
（共 31 条，此处仅展示前 30 条）
-/
protected theorem finite (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
    [IsDomain B] [MulSemiringAction G B] [IsGaloisGroup G R B] : Finite G := by
  let A : Subring B := (algebraMap R B).range
  let := FractionRing.liftAlgebra A (FractionRing B)
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  let : Algebra R A := (algebraMap R B).rangeRestrict.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite A B := Module.Finite.of_restrictScalars_finite R A B
  have := IsGaloisGroup.to_isFractionRing_of_isIntegral G A B (FractionRing A) (FractionRing B)
  apply Nat.finite_of_card_ne_zero
  rw [card_eq_finrank G (FractionRing A) (FractionRing B)]
  exact Module.finrank_pos.ne'

section IsDomain

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
  [MulSemiringAction G B] [MulSemiringAction G' B] [IsGaloisGroup G A B] [IsGaloisGroup G' A B]
  [Finite G] [Finite G']

/-- The cardinality of a Galois group of `B/A` equals the rank of `B` as an `A`-module.

See `IsGaloisGroup.card_eq_finrank`, a field-theoretic version that does not assume finiteness. -/
/-
**IsGaloisGroup.card_eq_finrank'** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：card_eq_finrank' : Nat.card G = Module.finrank A B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDomain.of_faithfulSMul`：IsDomain.of_faithfulSMul [IsDomain A] : IsDoma
in R
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGaloisGroup.card_eq_finrank`：card_eq_finrank [IsGaloisGroup G K L] : N
at.card G = Module.finrank K L
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsFractionRing.finrank_eq`：∀ (A : Type u_1) (K : Type u_2) (B : Type u_3
) (L : Type u_4) [inst : CommRing A] [inst_1 : CommRing K]   [inst_2 : CommRing 
B] [inst_3 : Co…

--- 原说明 ---
The cardinality of a Galois group of `B/A` equals the rank of `B` as an `A`-modu
le.

See `IsGaloisGroup.card_eq_finrank`, a field-theoretic version that does not ass
ume finiteness.
-/
theorem card_eq_finrank' : Nat.card G = Module.finrank A B := by
  have := IsDomain.of_faithfulSMul A B
  let := FractionRing.liftAlgebra A (FractionRing B)
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  rw [IsGaloisGroup.card_eq_finrank G (FractionRing A) (FractionRing B),
    IsFractionRing.finrank_eq A (FractionRing A) B (FractionRing B)]

@[simp]
/-
**IsGaloisGroup.map_mulEquivAlgEquiv_fixingSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `I
sGaloisGroup`。
形式化陈述：map_mulEquivAlgEquiv_fixingSubgroup [IsGaloisGroup G K L] (F : Intermediat
eField K L) : (fixingSubgroup G (F : Set L)).map (mulEquivAlgEquiv G K L) = F.fi
xingSubgroup
参数：F : IntermediateField K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsGaloisGroup.mulEquivAlgEquiv_apply_apply`：∀ (G : Type u_1) [inst : Gro
up G] (A : Type u_2) (B : Type u_3) [inst_1 : CommRing A] [inst_2 : CommRing B] 
  [inst_3 : IsDomain B] [inst_4 …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_mulEquivAlgEquiv_fixingSubgroup [IsGaloisGroup G K L] (F : IntermediateField K L) :
    (fixingSubgroup G (F : Set L)).map (mulEquivAlgEquiv G K L) = F.fixingSubgroup := by
  ext g
  obtain ⟨g, rfl⟩ := (mulEquivAlgEquiv G K L).surjective g
  simp [mem_fixingSubgroup_iff]

/-- If `G` and `G'` are finite Galois groups for `B/A`, then `G` is isomorphic to `G'`. -/
/-
**IsGaloisGroup.mulEquivCongr** 是 Mathlib 中的一个定义，位于命名空间 `IsGaloisGroup`。
形式化陈述：mulEquivCongr : G ≃* G'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` and `G'` are finite Galois groups for `B/A`, then `G` is isomorphic to `G
'`.
-/
noncomputable def mulEquivCongr : G ≃* G' :=
  (mulEquivAlgEquiv G A B).trans (mulEquivAlgEquiv G' A B).symm

@[simp]
/-
**IsGaloisGroup.mulEquivCongr_apply_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGrou
p`。
形式化陈述：mulEquivCongr_apply_smul (g : G) (x : B) : mulEquivCongr G G' A B g • x = 
g • x
参数：g : G；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgEquiv.ext_iff`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst 
: CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Alge
bra R …
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
-/
theorem mulEquivCongr_apply_smul (g : G) (x : B) : mulEquivCongr G G' A B g • x = g • x :=
  AlgEquiv.ext_iff.mp ((mulEquivAlgEquiv G' A B).apply_symm_apply (mulEquivAlgEquiv G A B g)) x

@[simp]
/-
**IsGaloisGroup.mulEquivCongr_symm_apply_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloi
sGroup`。
形式化陈述：mulEquivCongr_symm_apply_smul (g : G') (x : B) : (mulEquivCongr G G' A B).
symm g • x = g • x
参数：g : G'；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGaloisGroup.mulEquivCongr_apply_smul`：mulEquivCongr_apply_smul (g : G)
 (x : B) : mulEquivCongr G G' A B g • x = g • x
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
-/
theorem mulEquivCongr_symm_apply_smul (g : G') (x : B) :
    (mulEquivCongr G G' A B).symm g • x = g • x := by
  rw [← mulEquivCongr_apply_smul G G' A B, MulEquiv.apply_symm_apply]

@[deprecated (since := "2026-06-19")] alias mulEquivCongr' := mulEquivCongr
@[deprecated (since := "2026-06-19")] alias mulEquivCongr'_apply_smul := mulEquivCongr_apply_smul
/-
**IsGaloisGroup.mulEquivCongr_mapSubgroup_fixingSubgroup** 是 Mathlib 中的一个定理，位于命名
空间 `IsGaloisGroup`。
形式化陈述：mulEquivCongr_mapSubgroup_fixingSubgroup (S : Set B) : (fixingSubgroup G S
).map (mulEquivCongr G G' A B) = fixingSubgroup G' S
参数：S : Set B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f : G ≃* N) (
K : Subgroup G) : K.map f = K.comap (G
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsGaloisGroup.mulEquivCongr_symm_apply_smul`：mulEquivCongr_symm_apply_sm
ul (g : G') (x : B) : (mulEquivCongr G G' A B).symm g • x = g • x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mulEquivCongr_mapSubgroup_fixingSubgroup (S : Set B) :
    (fixingSubgroup G S).map (mulEquivCongr G G' A B) = fixingSubgroup G' S := by
  ext g
  simp [Subgroup.map_equiv_eq_comap_symm, mem_fixingSubgroup_iff]

end IsDomain

variable (H H' : Subgroup G) (F F' : IntermediateField K L)

/-
**IsGaloisGroup.subgroup** 是 Mathlib 中的一个实例，位于命名空间 `IsGaloisGroup`。
形式化陈述：subgroup [hGKL : IsGaloisGroup G K L] : IsGaloisGroup H (FixedPoints.inter
mediateField H : IntermediateField K L) L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance subgroup [hGKL : IsGaloisGroup G K L] :
    IsGaloisGroup H (FixedPoints.intermediateField H : IntermediateField K L) L :=
  inferInstanceAs (IsGaloisGroup H (FixedPoints.subalgebra K L H) L)

open IntermediateField in
/-
**IsGaloisGroup.fixedPoints_of_isGaloisGroup** 是 Mathlib 中的一个定理，位于命名空间 `IsGalois
Group`。
形式化陈述：fixedPoints_of_isGaloisGroup [hGKL : IsGaloisGroup G K L] [hHFL : IsGalois
Group H F L] : FixedPoints.intermediateField H = F
该定理/引理给出了一组等式。
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `IntermediateField.ext_iff`：∀ {K : Type u_1} {L : Type u_2} [inst : Field
 K] [inst_1 : Field L] [inst_2 : Algebra K L]   {S T : IntermediateField K L}, S
 = T ↔ ∀ (x : L…
· 使用定理 `Algebra.IsInvariant.isInvariant`：∀ {A : Type u_1} {B : Type u_2} {G : Ty
pe u_3} {inst : CommSemiring A} {inst_1 : Semiring B} {inst_2 : Algebra A B}   {
inst_3 : Group G} {in…
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsGaloisGroup.fixedPoints_eq_bot`：fixedPoints_eq_bot [IsGaloisGroup G K 
L] : FixedPoints.intermediateField G = (⊥ : IntermediateField K L)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.restrictScalars_bot_eq_self`：restrictScalars_bot_eq_se
lf (K : IntermediateField F E) : (⊥ : IntermediateField K E).restrictScalars _ =
 K
-/
theorem fixedPoints_of_isGaloisGroup [hGKL : IsGaloisGroup G K L] [hHFL : IsGaloisGroup H F L] :
    FixedPoints.intermediateField H = F := by
  refine IntermediateField.ext_iff.mpr fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := hHFL.isInvariant.isInvariant x hx
    exact a.prop
  · have := congr_arg (restrictScalars K) <| IsGaloisGroup.fixedPoints_eq_bot H F L
    rw [restrictScalars_bot_eq_self] at this
    rwa [← this] at hx
/-
**IsGaloisGroup.of_fixedPoints_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：of_fixedPoints_eq [hGKL : IsGaloisGroup G K L] (hF : FixedPoints.intermedi
ateField H = F) : IsGaloisGroup H F L
参数：hF : FixedPoints.intermediateField H = F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem of_fixedPoints_eq [hGKL : IsGaloisGroup G K L] (hF : FixedPoints.intermediateField H = F) :
    IsGaloisGroup H F L := by
  rw [eq_comm] at hF
  convert! IsGaloisGroup.subgroup G K L H

variable {G K L H F} in
/-
**IsGaloisGroup.subgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：subgroup_iff [hGKL : IsGaloisGroup G K L] : IsGaloisGroup H F L ↔ FixedPoi
nts.intermediateField H = F
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
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `IsGaloisGroup.fixedPoints_of_isGaloisGroup`：fixedPoints_of_isGaloisGroup
 [hGKL : IsGaloisGroup G K L] [hHFL : IsGaloisGroup H F L] : FixedPoints.interme
diateField H = F
· 使用定理 `IsGaloisGroup.of_fixedPoints_eq`：of_fixedPoints_eq [hGKL : IsGaloisGroup
 G K L] (hF : FixedPoints.intermediateField H = F) : IsGaloisGroup H F L
-/
theorem subgroup_iff [hGKL : IsGaloisGroup G K L] :
    IsGaloisGroup H F L ↔ FixedPoints.intermediateField H = F :=
  ⟨fun _ ↦ fixedPoints_of_isGaloisGroup G K L H F, fun h ↦ of_fixedPoints_eq G K L H F h⟩

@[simp]
/-
**IsGaloisGroup.finrank_fixedPoints_eq_card_subgroup** 是 Mathlib 中的一个定理，位于命名空间 `
IsGaloisGroup`。
形式化陈述：finrank_fixedPoints_eq_card_subgroup [IsGaloisGroup G K L] : Module.finran
k (FixedPoints.intermediateField H : IntermediateField K L) L = Nat.card H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `IsGaloisGroup.card_eq_finrank`：card_eq_finrank [IsGaloisGroup G K L] : N
at.card G = Module.finrank K L
-/
theorem finrank_fixedPoints_eq_card_subgroup [IsGaloisGroup G K L] :
    Module.finrank (FixedPoints.intermediateField H : IntermediateField K L) L = Nat.card H :=
  (card_eq_finrank H (FixedPoints.intermediateField H) L).symm

variable {G K L} in
/-
**IsGaloisGroup.of_mulEquiv_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：of_mulEquiv_algEquiv [IsGalois K L] (e : G ≃* Gal(L/K)) (he : forall g x, 
e g x = g • x) : IsGaloisGroup G K L
参数：e : G ≃* Gal(L/K)；he : forall g x, e g x = g • x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.of_mulEquiv`：of_mulEquiv [hG : IsGaloisGroup G A B] {H : T
ype*} [Group H] [MulSemiringAction H B] (e : H ≃* G) (he : forall h (x : B), (e 
h) • x = h • x)…
-/
theorem of_mulEquiv_algEquiv [IsGalois K L] (e : G ≃* Gal(L/K)) (he : ∀ g x, e g x = g • x) :
    IsGaloisGroup G K L := .of_mulEquiv e he
/-
**IsGaloisGroup.fixedPoints** 是 Mathlib 中的一个实例，位于命名空间 `IsGaloisGroup`。
形式化陈述：fixedPoints [Finite G] [FaithfulSMul G L] : IsGaloisGroup G (FixedPoints.s
ubfield G L) L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.of_mulEquiv_algEquiv`：of_mulEquiv_algEquiv [IsGalois K L] 
(e : G ≃* Gal(L/K)) (he : forall g x, e g x = g • x) : IsGaloisGroup G K L
-/
instance fixedPoints [Finite G] [FaithfulSMul G L] :
    IsGaloisGroup G (FixedPoints.subfield G L) L :=
  of_mulEquiv_algEquiv (FixedPoints.toAlgAutMulEquiv _ _) fun _ _ ↦ rfl
/-
**IsGaloisGroup.intermediateField** 是 Mathlib 中的一个实例，位于命名空间 `IsGaloisGroup`。
形式化陈述：intermediateField [Finite G] [hGKL : IsGaloisGroup G K L] : IsGaloisGroup 
(fixingSubgroup G (F : Set L)) F L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsGaloisGroup.map_mulEquivAlgEquiv_fixingSubgroup`：map_mulEquivAlgEquiv_
fixingSubgroup [IsGaloisGroup G K L] (F : IntermediateField K L) : (fixingSubgro
up G (F : Set L)).map (mulEquivAlgEquiv…
· 使用定理 `IsGaloisGroup.isGalois`：isGalois [Finite G] [IsGaloisGroup G K L] : IsGa
lois K L
· 使用定理 `IsGaloisGroup.of_mulEquiv_algEquiv`：of_mulEquiv_algEquiv [IsGalois K L] 
(e : G ≃* Gal(L/K)) (he : forall g x, e g x = g • x) : IsGaloisGroup G K L
· 使用定理 `IsGalois.tower_top_intermediateField`：∀ {F : Type u_1} {E : Type u_3} [i
nst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] (K : IntermediateField 
F E)   [IsGalois F E], IsG…
-/
instance intermediateField [Finite G] [hGKL : IsGaloisGroup G K L] :
    IsGaloisGroup (fixingSubgroup G (F : Set L)) F L :=
  let e := ((mulEquivAlgEquiv G K L).subgroupMap (fixingSubgroup G (F : Set L))).trans <|
    (MulEquiv.subgroupCongr (map_mulEquivAlgEquiv_fixingSubgroup ..)).trans <|
    IntermediateField.fixingSubgroupEquiv F
  have := hGKL.isGalois
  .of_mulEquiv_algEquiv e fun _ _ ↦ rfl

include K in
/-- If `G` is a Galois group on `L/K` and `L/E/K` is a tower of field extensions,
then the fixing subgroup of the image of `E` in `L` is a Galois group on `L/E`. -/
/-
**IsGaloisGroup.of_isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：of_isScalarTower [Finite G] [IsGaloisGroup G K L] (E : Type*) [Field E] [A
lgebra K E] [Algebra E L] [IsScalarTower K E L] : IsGaloisGroup (fixingSubgroup 
G (Set.range (algebraMap E L))) E L
参数：E : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.toAlgHom_fieldRange`：IsScalarTower.toAlgHom_fieldRange [Al
gebra L L'] [IsScalarTower K L L'] : (IsScalarTower.toAlgHom K L L').fieldRange 
= Set.range (algebraMap…
· 使用定理 `IsGaloisGroup.of_ringEquiv`：of_ringEquiv [hG : IsGaloisGroup G A B] [Com
mSemiring A'] [Algebra A' B] (e : A ≃+* A') (he : forall a, algebraMap A' B (e a
) = algebraMap A…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.coe_toAlgHom`：coe_toAlgHom : ↑(toAlgHom R S A) = algebraMa
p S A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `AlgHom.equivFieldRange_apply_coe`：∀ {K : Type u_1} {L : Type u_2} {L' : 
Type u_3} [inst : Field K] [inst_1 : Field L] [inst_2 : Field L']   [inst_3 : Al
gebra K L] [inst_4 : A…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `G` is a Galois group on `L/K` and `L/E/K` is a tower of field extensions,
then the fixing subgroup of the image of `E` in `L` is a Galois group on `L/E`.
-/
theorem of_isScalarTower [Finite G] [IsGaloisGroup G K L] (E : Type*) [Field E] [Algebra K E]
    [Algebra E L] [IsScalarTower K E L] :
    IsGaloisGroup (fixingSubgroup G (Set.range (algebraMap E L))) E L := by
  rw [← IsScalarTower.toAlgHom_fieldRange K E L]
  refine IsGaloisGroup.of_ringEquiv _ _ _ L
    (AlgHom.equivFieldRange (IsScalarTower.toAlgHom K E L)).toRingEquiv.symm fun ⟨_, ⟨x, rfl⟩⟩ ↦ ?_
  simp [AlgEquiv.symm_apply_eq, Subtype.ext_iff]

@[simp]
/-
**IsGaloisGroup.card_fixingSubgroup_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 `IsGalo
isGroup`。
形式化陈述：card_fixingSubgroup_eq_finrank [Finite G] [IsGaloisGroup G K L] : Nat.card
 (fixingSubgroup G (F : Set L)) = Module.finrank F L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.card_eq_finrank`：card_eq_finrank [IsGaloisGroup G K L] : N
at.card G = Module.finrank K L
-/
theorem card_fixingSubgroup_eq_finrank [Finite G] [IsGaloisGroup G K L] :
    Nat.card (fixingSubgroup G (F : Set L)) = Module.finrank F L :=
  card_eq_finrank ..

section GaloisCorrespondence

/-
**IsGaloisGroup.fixingSubgroup_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup
`。
形式化陈述：fixingSubgroup_le_of_le (h : F <= F') : fixingSubgroup G (F' : Set L) <= f
ixingSubgroup G (F : Set L)
参数：h : F <= F'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fixingSubgroup_le_of_le (h : F ≤ F') :
    fixingSubgroup G (F' : Set L) ≤ fixingSubgroup G (F : Set L) :=
  fun _ hσ ⟨x, hx⟩ ↦ hσ ⟨x, h hx⟩

section SMulCommClass

variable [SMulCommClass G K L]

@[simp]
/-
**IsGaloisGroup.fixingSubgroup_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：fixingSubgroup_bot : fixingSubgroup G ((⊥ : IntermediateField K L) : Set L
) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_algebraMap`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Algebra R A] {α : Type u_2}   [inst_3 : Monoid α] [
inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fixingSubgroup_bot : fixingSubgroup G ((⊥ : IntermediateField K L) : Set L) = ⊤ := by
  simp [Subgroup.ext_iff, mem_fixingSubgroup_iff, IntermediateField.mem_bot]

@[simp]
/-
**IsGaloisGroup.fixedPoints_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：fixedPoints_bot : (FixedPoints.intermediateField (⊥ : Subgroup G) : Interm
ediateField K L) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem fixedPoints_bot :
    (FixedPoints.intermediateField (⊥ : Subgroup G) : IntermediateField K L) = ⊤ := by
  simp [IntermediateField.ext_iff]
/-
**IsGaloisGroup.le_fixedPoints_iff_le_fixingSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `
IsGaloisGroup`。
形式化陈述：le_fixedPoints_iff_le_fixingSubgroup : F <= FixedPoints.intermediateField 
H ↔ H <= fixingSubgroup G (F : Set L)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem le_fixedPoints_iff_le_fixingSubgroup :
    F ≤ FixedPoints.intermediateField H ↔ H ≤ fixingSubgroup G (F : Set L) :=
  ⟨fun h g hg x ↦ h x.2 ⟨g, hg⟩, fun h x hx g ↦ h g.2 ⟨x, hx⟩⟩
/-
**IsGaloisGroup.fixedPoints_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：fixedPoints_le_of_le (h : H <= H') : FixedPoints.intermediateField H' <= (
FixedPoints.intermediateField H : IntermediateField K L)
参数：h : H <= H'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fixedPoints_le_of_le (h : H ≤ H') :
    FixedPoints.intermediateField H' ≤ (FixedPoints.intermediateField H : IntermediateField K L) :=
  fun _ hσ ⟨x, hx⟩ ↦ hσ ⟨x, h hx⟩

end SMulCommClass

section IsGaloisGroup

variable [hGKL : IsGaloisGroup G K L]

-- this can't be a simp-lemma since the left-hand side is not in simp normal form
-- and if the theorem was `fixingSubgroup G Set.univ = ⊥` then `K` couldn't be inferred
/-
**IsGaloisGroup.fixingSubgroup_top** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：fixingSubgroup_top : fixingSubgroup G ((⊤ : IntermediateField K L) : Set L
) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.faithful`：∀ {G : Type u_1} (A : Type u_2) {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `MulAction.fixedBy_eq_univ_iff_eq_one`：fixedBy_eq_univ_iff_eq_one {m : M}
 : fixedBy α m = Set.univ ↔ m = 1
-/
theorem fixingSubgroup_top : fixingSubgroup G ((⊤ : IntermediateField K L) : Set L) = ⊥ := by
  have := hGKL.faithful
  ext; simpa [mem_fixingSubgroup_iff, Set.ext_iff] using MulAction.fixedBy_eq_univ_iff_eq_one

@[simp]
/-
**IsGaloisGroup.fixedPoints_top** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：fixedPoints_top : (FixedPoints.intermediateField (⊤ : Subgroup G) : Interm
ediateField K L) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsGaloisGroup.fixedPoints_eq_bot`：fixedPoints_eq_bot [IsGaloisGroup G K 
L] : FixedPoints.intermediateField G = (⊥ : IntermediateField K L)
-/
theorem fixedPoints_top :
    (FixedPoints.intermediateField (⊤ : Subgroup G) : IntermediateField K L) = ⊥ := by
  convert! IsGaloisGroup.fixedPoints_eq_bot G K L
  ext; simp

/-- The Galois correspondence from intermediate fields to subgroups. -/
/-
**IsGaloisGroup.intermediateFieldEquivSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `IsGalo
isGroup`。
形式化陈述：intermediateFieldEquivSubgroup [Finite G] : IntermediateField K L ≃o (Subg
roup G)ᵒᵈ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.isGalois`：isGalois [Finite G] [IsGaloisGroup G K L] : IsGa
lois K L
· 使用定理 `IsGaloisGroup.finiteDimensional`：finiteDimensional [Finite G] [IsGaloisG
roup G K L] : FiniteDimensional K L

--- 原说明 ---
The Galois correspondence from intermediate fields to subgroups.
-/
noncomputable def intermediateFieldEquivSubgroup [Finite G] :
    IntermediateField K L ≃o (Subgroup G)ᵒᵈ :=
  have := isGalois G K L
  have := finiteDimensional G K L
  IsGalois.intermediateFieldEquivSubgroup.trans <| (mulEquivAlgEquiv G K L).comapSubgroup.dual
/-
**IsGaloisGroup.intermediateFieldEquivSubgroup_apply** 是 Mathlib 中的一个定理，位于命名空间 `
IsGaloisGroup`。
形式化陈述：∀ (G : Type u_1) (K : Type u_3) (L : Type u_4) [inst : Group G] [inst_1 : 
Field K] [inst_2 : Field L]   [inst_3 : Algebra K L] [inst_4 : MulSemiringAction
 G L] [hGKL : IsGaloisGroup G K L] [inst_5 : Finite G]   {F : IntermediateField 
K L},   (IsGaloisGroup.intermediateFieldEquivSubgroup G K L) F = OrderDual.toDua
l (fixingSubgroup G ↑F)
参数：G : Type u_1；K : Type u_3；L : Type u_4；IsGaloisGroup.intermediateFieldEquivSu
bgroup G K L；fixingSubgroup G ↑F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem intermediateFieldEquivSubgroup_apply [Finite G] {F} :
    intermediateFieldEquivSubgroup G K L F = .toDual (fixingSubgroup G (F : Set L)) := rfl
/-
**IsGaloisGroup.ofDual_intermediateFieldEquivSubgroup_apply** 是 Mathlib 中的一个定理，位
于命名空间 `IsGaloisGroup`。
形式化陈述：ofDual_intermediateFieldEquivSubgroup_apply [Finite G] {F} : (intermediate
FieldEquivSubgroup G K L F).ofDual = fixingSubgroup G (F : Set L)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_intermediateFieldEquivSubgroup_apply [Finite G] {F} :
    (intermediateFieldEquivSubgroup G K L F).ofDual = fixingSubgroup G (F : Set L) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**IsGaloisGroup.intermediateFieldEquivSubgroup_symm_apply** 是 Mathlib 中的一个定理，位于命
名空间 `IsGaloisGroup`。
形式化陈述：∀ (G : Type u_1) (K : Type u_3) (L : Type u_4) [inst : Group G] [inst_1 : 
Field K] [inst_2 : Field L]   [inst_3 : Algebra K L] [inst_4 : MulSemiringAction
 G L] [hGKL : IsGaloisGroup G K L] [inst_5 : Finite G]   {H : (Subgroup G)ᵒᵈ},  
 (IsGaloisGroup.intermediateFieldEquivSubgroup G K L).symm H = FixedPoints.inter
mediateField ↥(OrderDual.ofDual H)
参数：G : Type u_1；K : Type u_3；L : Type u_4；Subgroup G；IsGaloisGroup.intermediateF
ieldEquivSubgroup G K L；OrderDual.ofDual H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsGaloisGroup.finiteDimensional`：finiteDimensional [Finite G] [IsGaloisG
roup G K L] : FiniteDimensional K L
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGaloisGroup.isGalois`：isGalois [Finite G] [IsGaloisGroup G K L] : IsGa
lois K L
· 使用定理 `MulEquiv.comapSubgroup_apply`：∀ {G : Type u_1} [inst : Group G] {H : Typ
e u_5} [inst_1 : Group H] (f : G ≃* H) (H_1 : Subgroup H),   f.comapSubgroup H_1
 = Subgroup.comap …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
· 使用定理 `IsGaloisGroup.mulEquivAlgEquiv_apply_apply`：∀ (G : Type u_1) [inst : Gro
up G] (A : Type u_2) (B : Type u_3) [inst_1 : CommRing A] [inst_2 : CommRing B] 
  [inst_3 : IsDomain B] [inst_4 …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] theorem intermediateFieldEquivSubgroup_symm_apply [Finite G] {H} :
    (intermediateFieldEquivSubgroup G K L).symm H = FixedPoints.intermediateField H.ofDual := by
  obtain ⟨H, rfl⟩ := OrderDual.toDual.surjective H
  simp [IntermediateField.ext_iff, intermediateFieldEquivSubgroup,
    (mulEquivAlgEquiv G K L).surjective.forall, -mulEquivAlgEquiv_symm_apply]
/-
**IsGaloisGroup.intermediateFieldEquivSubgroup_symm_apply_toDual** 是 Mathlib 中的一
个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：intermediateFieldEquivSubgroup_symm_apply_toDual [Finite G] {H} : (interme
diateFieldEquivSubgroup G K L).symm (.toDual H) = FixedPoints.intermediateField 
H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.intermediateFieldEquivSubgroup_symm_apply`：∀ (G : Type u_1
) (K : Type u_3) (L : Type u_4) [inst : Group G] [inst_1 : Field K] [inst_2 : Fi
eld L]   [inst_3 : Algebra K L] [inst_4 : Mul…
-/
theorem intermediateFieldEquivSubgroup_symm_apply_toDual [Finite G] {H} :
    (intermediateFieldEquivSubgroup G K L).symm (.toDual H) = FixedPoints.intermediateField H :=
  intermediateFieldEquivSubgroup_symm_apply ..

@[simp]
/-
**IsGaloisGroup.fixingSubgroup_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGr
oup`。
形式化陈述：fixingSubgroup_fixedPoints [Finite G] : fixingSubgroup G ((FixedPoints.int
ermediateField H : IntermediateField K L) : Set L) = H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGaloisGroup.intermediateFieldEquivSubgroup_symm_apply_toDual`：intermed
iateFieldEquivSubgroup_symm_apply_toDual [Finite G] {H} : (intermediateFieldEqui
vSubgroup G K L).symm (.toDual H) = FixedPoints.inte…
· 使用定理 `IsGaloisGroup.ofDual_intermediateFieldEquivSubgroup_apply`：ofDual_interm
ediateFieldEquivSubgroup_apply [Finite G] {F} : (intermediateFieldEquivSubgroup 
G K L F).ofDual = fixingSubgroup G (F : Set L)
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `OrderDual.ofDual_toDual`：∀ {α : Type u_1} (a : α), OrderDual.ofDual (Ord
erDual.toDual a) = a
-/
theorem fixingSubgroup_fixedPoints [Finite G] :
    fixingSubgroup G ((FixedPoints.intermediateField H : IntermediateField K L) : Set L) = H := by
  rw [← intermediateFieldEquivSubgroup_symm_apply_toDual,
    ← ofDual_intermediateFieldEquivSubgroup_apply,
    OrderIso.apply_symm_apply, OrderDual.ofDual_toDual]

@[simp]
/-
**IsGaloisGroup.fixedPoints_fixingSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGr
oup`。
形式化陈述：fixedPoints_fixingSubgroup [Finite G] : FixedPoints.intermediateField (fix
ingSubgroup G (F : Set L)) = F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGaloisGroup.ofDual_intermediateFieldEquivSubgroup_apply`：ofDual_interm
ediateFieldEquivSubgroup_apply [Finite G] {F} : (intermediateFieldEquivSubgroup 
G K L F).ofDual = fixingSubgroup G (F : Set L)
· 使用定理 `IsGaloisGroup.intermediateFieldEquivSubgroup_symm_apply`：∀ (G : Type u_1
) (K : Type u_3) (L : Type u_4) [inst : Group G] [inst_1 : Field K] [inst_2 : Fi
eld L]   [inst_3 : Algebra K L] [inst_4 : Mul…
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
-/
theorem fixedPoints_fixingSubgroup [Finite G] :
    FixedPoints.intermediateField (fixingSubgroup G (F : Set L)) = F := by
  rw [← ofDual_intermediateFieldEquivSubgroup_apply, ← intermediateFieldEquivSubgroup_symm_apply,
    OrderIso.symm_apply_apply]

/-- If `G` acts as a Galois group on `L/K` and the subgroup `H` acts as a Galois group on `L/B`,
then the fixed points of `H` equals the range of `algebraMap B L`. -/
/-
**IsGaloisGroup.fixedPoints_eq_range_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsGal
oisGroup`。
形式化陈述：fixedPoints_eq_range_algebraMap (B : Type*) [CommSemiring B] [Algebra B L]
 [IsGaloisGroup H B L] : (FixedPoints.intermediateField H : IntermediateField K 
L) = Set.range (algebraMap B L)
参数：B : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `FixedPoints.mem_intermediateField_iff`：∀ {F : Type u_1} [inst : Field F]
 {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] {M : Type u_3}   [inst
_3 : Monoid M] [inst_4 : Mu…
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Algebra.IsInvariant.isInvariant`：∀ {A : Type u_1} {B : Type u_2} {G : Ty
pe u_3} {inst : CommSemiring A} {inst_1 : Semiring B} {inst_2 : Algebra A B}   {
inst_3 : Group G} {in…
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
· 使用定理 `smul_algebraMap`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Algebra R A] {α : Type u_2}   [inst_3 : Monoid α] [
inst_…

--- 原说明 ---
If `G` acts as a Galois group on `L/K` and the subgroup `H` acts as a Galois gro
up on `L/B`,
then the fixed points of `H` equals the range of `algebraMap B L`.
-/
theorem fixedPoints_eq_range_algebraMap (B : Type*)
    [CommSemiring B] [Algebra B L] [IsGaloisGroup H B L] :
    (FixedPoints.intermediateField H : IntermediateField K L) = Set.range (algebraMap B L) := by
  ext
  rw [SetLike.mem_coe, FixedPoints.mem_intermediateField_iff, Set.mem_range]
  refine ⟨IsGaloisGroup.isInvariant.isInvariant _, ?_⟩
  rintro ⟨x, rfl⟩ h
  exact smul_algebraMap h x

include K in
/-- If `G` acts as a Galois group on `L/K` and the subgroup `H` acts as a Galois group on `L/B`,
then the fixing subgroup of `algebraMap B L` inside `G` equals `H`.
See `fixingSubgroup_range_algebraMap` for a more general version. -/
/-
**IsGaloisGroup.fixingSubgroup_range_algebraMap'** 是 Mathlib 中的一个定理，位于命名空间 `IsGa
loisGroup`。
形式化陈述：fixingSubgroup_range_algebraMap' [Finite G] (B : Type*) [CommSemiring B] [
Algebra B L] [IsGaloisGroup H B L] : fixingSubgroup G (Set.range (algebraMap B L
)) = H
参数：B : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGaloisGroup.fixedPoints_eq_range_algebraMap`：fixedPoints_eq_range_alge
braMap (B : Type*) [CommSemiring B] [Algebra B L] [IsGaloisGroup H B L] : (Fixed
Points.intermediateField H : Interm…
· 使用定理 `IsGaloisGroup.fixingSubgroup_fixedPoints`：fixingSubgroup_fixedPoints [Fi
nite G] : fixingSubgroup G ((FixedPoints.intermediateField H : IntermediateField
 K L) : Set L) = H

--- 原说明 ---
If `G` acts as a Galois group on `L/K` and the subgroup `H` acts as a Galois gro
up on `L/B`,
then the fixing subgroup of `algebraMap B L` inside `G` equals `H`.
See `fixingSubgroup_range_algebraMap` for a more general version.
-/
theorem fixingSubgroup_range_algebraMap' [Finite G] (B : Type*) [CommSemiring B] [Algebra B L]
    [IsGaloisGroup H B L] :
    fixingSubgroup G (Set.range (algebraMap B L)) = H := by
  rw [← fixedPoints_eq_range_algebraMap G K L H, fixingSubgroup_fixedPoints]

attribute [local instance] FractionRing.liftAlgebra in
/-- If `G` acts on a domain `C` with `IsGaloisGroup G A C`, and a subgroup `H` acts on `C` with
`IsGaloisGroup H B C`, then the fixing subgroup of `algebraMap B C` equals `H`. -/
/-
**IsGaloisGroup.fixingSubgroup_range_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsGal
oisGroup`。
形式化陈述：fixingSubgroup_range_algebraMap [Finite G] (A B C : Type*) (H : Subgroup G
) [CommRing A] [CommRing B] [CommRing C] [IsDomain C] [Algebra A C] [FaithfulSMu
l A C] [MulSemiringAction G C] [hGAC : IsGaloisGroup G A C] [Algebra B C] [Faith
fulSMul B C] [hH : IsGaloisGroup H B C] : fixingSubgroup G (Set.range (algebraMa
p B C)) = H
参数：A B C : Type*；H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGaloisGroup.fixingSubgroup_range_algebraMap'`：fixingSubgroup_range_alg
ebraMap' [Finite G] (B : Type*) [CommSemiring B] [Algebra B L] [IsGaloisGroup H 
B L] : fixingSubgroup G (Set.range (…
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `algebraMap.smul'`：algebraMap.smul' [Monoid A] [MulDistribMulAction A C] 
[SMulDistribClass A B C] : algebraMap B C (a • b) = a • (algebraMap B C b)
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `smul_div₀'`：smul_div₀' (g : α) (x y : β) : g • (x / y) = (g • x) / (g • 
y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …

--- 原说明 ---
If `G` acts on a domain `C` with `IsGaloisGroup G A C`, and a subgroup `H` acts 
on `C` with
`IsGaloisGroup H B C`, then the fixing subgroup of `algebraMap B C` equals `H`.
-/
theorem fixingSubgroup_range_algebraMap [Finite G] (A B C : Type*) (H : Subgroup G)
    [CommRing A] [CommRing B] [CommRing C] [IsDomain C]
    [Algebra A C] [FaithfulSMul A C] [MulSemiringAction G C] [hGAC : IsGaloisGroup G A C]
    [Algebra B C] [FaithfulSMul B C] [hH : IsGaloisGroup H B C] :
    fixingSubgroup G (Set.range (algebraMap B C)) = H := by
  have : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  have : IsDomain A := (FaithfulSMul.algebraMap_injective A C).isDomain
  let K := FractionRing A
  let L := FractionRing C
  let : MulSemiringAction G L := IsFractionRing.mulSemiringAction G C L
  have : IsGaloisGroup H (FractionRing B) L := IsGaloisGroup.toFractionRing H B C
  rw [← fixingSubgroup_range_algebraMap' G K L H (FractionRing B)]
  ext g
  simp only [mem_fixingSubgroup_iff, Set.mem_range]
  refine ⟨?_, ?_⟩
  · rintro h _ ⟨x, rfl⟩
    have {x} : g • (algebraMap B L) x = (algebraMap B L) x := by
      rw [IsScalarTower.algebraMap_apply B C L, ← algebraMap.smul', h _ ⟨x, rfl⟩]
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective B x
    simp only [map_div₀, ← IsScalarTower.algebraMap_apply, smul_div₀', this]
  · rintro h _ ⟨x, rfl⟩
    apply FaithfulSMul.algebraMap_injective C L
    rw [algebraMap.smul']
    apply h
    use algebraMap B (FractionRing B) x
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

open Pointwise in
/-- If `G` is a finite Galois group for `L/K`, `H` is a Galois group for `L/E`, and `E/K` is
Galois, then `H` is a normal subgroup of `G`. -/
/-
**IsGaloisGroup.normal_of_isGalois** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：normal_of_isGalois (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsSc
alarTower K E L] [Finite G] [IsGaloisGroup H E L] [IsGalois K E] : H.Normal
参数：E : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGalois.of_algEquiv`：IsGalois.of_algEquiv [IsGalois F E] (f : E ≃ₐ[F] E
') : IsGalois F E'
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsGaloisGroup.isGalois`：isGalois [Finite G] [IsGaloisGroup G K L] : IsGa
lois K L
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGaloisGroup.fixingSubgroup_fixedPoints`：fixingSubgroup_fixedPoints [Fi
nite G] : fixingSubgroup G ((FixedPoints.intermediateField H : IntermediateField
 K L) : Set L) = H
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsGaloisGroup.subgroup_iff`：subgroup_iff [hGKL : IsGaloisGroup G K L] : 
IsGaloisGroup H F L ↔ FixedPoints.intermediateField H = F
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `IsGaloisGroup.mulEquivCongr_mapSubgroup_fixingSubgroup`：mulEquivCongr_ma
pSubgroup_fixingSubgroup (S : Set B) : (fixingSubgroup G S).map (mulEquivCongr G
 G' A B) = fixingSubgroup G' S
· 使用定理 `MulEquiv.normal_map_iff`：∀ {G : Type u_1} {G' : Type u_2} [inst : Group 
G] [inst_1 : Group G'] {f : G ≃* G'} {H : Subgroup G},   (Subgroup.map (↑f) H).N
ormal ↔ H.Nor…

--- 原说明 ---
If `G` is a finite Galois group for `L/K`, `H` is a Galois group for `L/E`, and 
`E/K` is
Galois, then `H` is a normal subgroup of `G`.
-/
theorem normal_of_isGalois (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [Finite G] [IsGaloisGroup H E L] [IsGalois K E] : H.Normal := by
  let F := (IsScalarTower.toAlgHom K E L).fieldRange
  have : IsGalois K F := .of_algEquiv (IsScalarTower.toAlgHom K E L).equivFieldRange
  have hFL : IsGaloisGroup H F L := inferInstanceAs (IsGaloisGroup H (algebraMap E L).range L)
  have := isGalois G K L
  have : Finite Gal(L/K) := Finite.of_equiv _ (mulEquivAlgEquiv G K L).toEquiv
  rw [← fixingSubgroup_fixedPoints G K L H, subgroup_iff.mp hFL,
    ← mulEquivCongr_mapSubgroup_fixingSubgroup Gal(L/K) G K, MulEquiv.normal_map_iff]
  exact IsGalois.fixingSubgroup_normal_of_isGalois F

end IsGaloisGroup

end GaloisCorrespondence

section Quotient

section Domain

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [IsDomain C] [Algebra A B]
    [Algebra A C] [Algebra B C] [FaithfulSMul A B] [FaithfulSMul B C] [IsScalarTower A B C]

/-- If `G` is a Galois group for `C/A`, and the normal subgroup `N ≤ G` is a Galois group for
`C/B`, then the quotient `G ⧸ N` is a Galois group for `B/A`. -/
/-
**quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is a Galois group for `C/A`, and the normal subgroup `N ≤ G` is a Galois 
group for
`C/B`, then the quotient `G ⧸ N` is a Galois group for `B/A`.
-/
theorem quotient [Finite G] (N : Subgroup G) [N.Normal] [MulSemiringAction G C]
    [hG : IsGaloisGroup G A C] [MulSemiringAction G B] [MulSemiringAction (G ⧸ N) B]
    [SMulCommClass (G ⧸ N) A B] [SMulDistribClass G B C] [IsScalarTower G (G ⧸ N) B]
    [IsGaloisGroup N B C] :
    IsGaloisGroup (G ⧸ N) A B where
  faithful.eq_of_smul_eq_smul := fun {g₁} {g₂} ↦ Quotient.inductionOn₂' g₁ g₂ fun g₁ g₂ h ↦ by
    have : FaithfulSMul A C := FaithfulSMul.trans A B C
    have h' : ∀ g : G, (∀ x : B, g • x = x) → g ∈ N := by
      simp [← fixingSubgroup_range_algebraMap G A B C N, mem_fixingSubgroup_iff, ← algebraMap.smul',
        (FaithfulSMul.algebraMap_injective B C).eq_iff]
    have {g : G} : Quotient.mk'' g = QuotientGroup.mk' N g := rfl
    simp_rw [← inv_smul_eq_iff, this, ← map_inv, smul_smul, ← map_mul,
      QuotientGroup.mk'_apply, MulAction.coe_quotient_smul] at h
    have := h' _ h
    rwa [QuotientGroup.eq, ← Subgroup.inv_mem_iff, mul_inv_rev, inv_inv]
  commutes := inferInstance
  isInvariant.isInvariant x h := by
    simp_rw [← (FaithfulSMul.algebraMap_injective B C).eq_iff, ← IsScalarTower.algebraMap_apply]
    apply hG.isInvariant.isInvariant (algebraMap B C x)
    intro g
    have := (FaithfulSMul.algebraMap_injective B C).eq_iff.mpr <| h g
    rwa [MulAction.coe_quotient_smul, algebraMap.smul'] at this

/-- If `G` is a Galois group for `C/A`, the normal subgroup `N ≤ G` is a Galois group for `C/B`,
and `G'` is a Galois group for `B/A`, then `G ⧸ N ≃* G'`. -/
/-
**quotientMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is a Galois group for `C/A`, the normal subgroup `N ≤ G` is a Galois grou
p for `C/B`,
and `G'` is a Galois group for `B/A`, then `G ⧸ N ≃* G'`.
-/
noncomputable def quotientMulEquiv [Finite G] [Finite G'] (N : Subgroup G) [N.Normal]
    [MulSemiringAction G C] [IsGaloisGroup G A C] [IsGaloisGroup N B C] [MulSemiringAction G' B]
    [IsGaloisGroup G' A B] :
    G ⧸ N ≃* G' :=
  haveI : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  letI := mulSemiringActionOfNormal G B C N
  letI := mulSemiringActionQuotient G B C N
  haveI := smulCommClassQuotient G A B C N
  haveI := quotient G A B C N
  mulEquivCongr (G ⧸ N) G' A B

@[simp]
/-
**algebraMap_quotientMulEquiv_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_quotientMulEquiv_smul [Finite G] [Finite G'] (N : Subgroup G) [N.Normal]
    [MulSemiringAction G C] [IsGaloisGroup G A C] [IsGaloisGroup N B C] [MulSemiringAction G' B]
    [IsGaloisGroup G' A B] (g : G) (x : B) :
    algebraMap B C (quotientMulEquiv G G' A B C N g • x) = g • algebraMap B C x := by
  have : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  let := mulSemiringActionOfNormal G B C N
  let := mulSemiringActionQuotient G B C N
  have := smulCommClassQuotient G A B C N
  have := quotient G A B C N
  rw [← algebraMap_smulOfNormal G B C N g x]
  congr
  apply mulEquivCongr_apply_smul

attribute [local instance] FractionRing.liftAlgebra in
/-- The restriction homomorphism from the Galois group of `C/A` to the Galois group of `B/A` where
`C/B/A` is a tower of domains with `C/A` and `B/A` Galois. -/
/-
**restrictHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction homomorphism from the Galois group of `C/A` to the Galois group 
of `B/A` where
`C/B/A` is a tower of domains with `C/A` and `B/A` Galois.
-/
noncomputable def restrictHom [Finite G] [Finite G'] [MulSemiringAction G C] [IsGaloisGroup G A C]
    [MulSemiringAction G' B] [IsGaloisGroup G' A B] :
    G →* G' :=
  haveI : IsDomain B := IsDomain.of_faithfulSMul B C
  haveI : IsDomain A := IsDomain.of_faithfulSMul A B
  haveI : FaithfulSMul A C := FaithfulSMul.trans A B C
  letI : MulSemiringAction G (FractionRing C) :=
    IsFractionRing.mulSemiringAction G C (FractionRing C)
  letI N := fixingSubgroup G (Set.range (algebraMap (FractionRing B) (FractionRing C)))
  haveI : IsGaloisGroup N (FractionRing B) (FractionRing C) :=
    of_isScalarTower G (FractionRing A) (FractionRing C) (FractionRing B)
  letI : MulSemiringAction G' (FractionRing B) :=
    IsFractionRing.mulSemiringAction G' B (FractionRing B)
  haveI := isGalois G' (FractionRing A) (FractionRing B)
  haveI : N.Normal := normal_of_isGalois G (FractionRing A) (FractionRing C) N (FractionRing B)
  (quotientMulEquiv G G' (FractionRing A) (FractionRing B) (FractionRing C) N).toMonoidHom.comp
    (QuotientGroup.mk' N)

attribute [local instance] FractionRing.liftAlgebra in
@[simp]
/-
**algebraMap_restrictHom_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_restrictHom_smul [Finite G] [Finite G'] [MulSemiringAction G C]
    [IsGaloisGroup G A C] [MulSemiringAction G' B] [IsGaloisGroup G' A B] (g : G) (x : B) :
    algebraMap B C (restrictHom G G' A B C g • x) = g • algebraMap B C x := by
  have : IsDomain B := IsDomain.of_faithfulSMul B C
  have : IsDomain A := IsDomain.of_faithfulSMul A B
  have : FaithfulSMul A C := FaithfulSMul.trans A B C
  let : MulSemiringAction G (FractionRing C) :=
    IsFractionRing.mulSemiringAction G C (FractionRing C)
  let : MulSemiringAction G' (FractionRing B) :=
    IsFractionRing.mulSemiringAction G' B (FractionRing B)
  apply FaithfulSMul.algebraMap_injective C (FractionRing C)
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply B (FractionRing B) (FractionRing C)]
  simp only [restrictHom, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe,
    QuotientGroup.coe_mk', Function.comp_apply]
  rw [algebraMap.smul', algebraMap_quotientMulEquiv_smul, ← IsScalarTower.algebraMap_apply,
    algebraMap.smul', ← IsScalarTower.algebraMap_apply]

attribute [local instance] FractionRing.liftAlgebra in
/-
**restrictHom_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictHom_surjective [Finite G] [Finite G'] [MulSemiringAction G C]
    [IsGaloisGroup G A C] [MulSemiringAction G' B] [IsGaloisGroup G' A B] :
    Function.Surjective (restrictHom G G' A B C) := by
  simpa [restrictHom] using QuotientGroup.mk_surjective

open Pointwise in
/-
**restrictHom_smul_under** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictHom_smul_under [Finite G] [Finite G'] [MulSemiringAction G C]
    [IsGaloisGroup G A C] [MulSemiringAction G' B] [IsGaloisGroup G' A B] (g : G) (I : Ideal C) :
    restrictHom G G' A B C g • I.under B = (g • I).under B := by
  simp [Ideal.ext_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]

end Domain

noncomputable section IntermediateField

variable (N : Subgroup G) [N.Normal] [IsGaloisGroup N F L]

/-- If `G` is a finite Galois group for `L/K` and `N` is a normal subgroup of `G` that is a
Galois group for `L/F`, then the quotient group `G ⧸ N` is a Galois group for `F/K`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is a finite Galois group for `L/K` and `N` is a normal subgroup of `G` th
at is a
Galois group for `L/F`, then the quotient group `G ⧸ N` is a Galois group for `F
/K`.
-/
instance [Finite G] [IsGaloisGroup G K L] : IsGaloisGroup (G ⧸ N) K F :=
  letI := smulOfNormal G F L N
  haveI := smulDistribClass_smulOfNormal G F L N
  letI := mulSemiringActionOfSmulDistribClass F L G
  quotient G K F L N

variable (E : IntermediateField K L) [hE : IsGaloisGroup H E L]

set_option backward.isDefEq.respectTransparency false in
/-- If `G` is a finite Galois group for `L/K`, `N` is a normal subgroup that is a Galois group for
`L/F`, and `H` is a subgroup that is a Galois group for `L/E` with `E ≤ F`, then the image of `H`
under the canonical quotient map `G → G ⧸ N` is a Galois group for `F/E`. -/
/-
**map_quotientMk'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is a finite Galois group for `L/K`, `N` is a normal subgroup that is a Ga
lois group for
`L/F`, and `H` is a subgroup that is a Galois group for `L/E` with `E ≤ F`, then
 the image of `H`
under the canonical quotient map `G → G ⧸ N` is a Galois group for `F/E`.
-/
theorem map_quotientMk' [Finite G] [IsGaloisGroup G K L] (h : E ≤ F) :
    letI : Algebra E F := (IntermediateField.inclusion h).toAlgebra
    IsGaloisGroup (H.map (QuotientGroup.mk' N)) E F :=
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  let : SMul G F := smulOfNormal G F L N
  have : SMulDistribClass G F L := smulDistribClass_smulOfNormal G F L N
  let := mulSemiringActionOfSmulDistribClass F L G
  have : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq' rfl
  { faithful := have := (inferInstance : IsGaloisGroup (G ⧸ N) K F).faithful; inferInstance
    commutes := ⟨by
      intro ⟨_, g, hg, rfl⟩ x y
      apply FaithfulSMul.algebraMap_injective F L
      simpa [MulAction.subgroup_smul_def, algebraMap.coe_smul', algebraMap.coe_smul]
        using hE.commutes.smul_comm ⟨g, hg⟩ x (y : L)⟩
    isInvariant := ⟨fun x h ↦ by
      obtain ⟨a, ha⟩ := hE.isInvariant.isInvariant (algebraMap F L x) (by
        rintro ⟨g, hg⟩
        rw [MulAction.subgroup_smul_def, ← algebraMap.smul']
        exact congr_arg (algebraMap F L) <| h ⟨g, ⟨g, hg, rfl⟩⟩)
      exact ⟨a, FaithfulSMul.algebraMap_injective F L
        (by rw [← IsScalarTower.algebraMap_apply, ha])⟩⟩ }

@[deprecated (since := "2026-04-21")] alias quotientMap := map_quotientMk'

end IntermediateField

end Quotient

end IsGaloisGroup

