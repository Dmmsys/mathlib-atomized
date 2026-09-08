/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.FieldTheory.Fixed
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Invariant.Defs

/-!
# Invariant Extensions of Rings

Given an extension of rings `B/A` and an action of `G` on `B`, we introduce a predicate
`Algebra.IsInvariant A B G` which states that every fixed point of `B` lies in the image of `A`.

The main application is in algebraic number theory, where `G := Gal(L/K)` is the Galois group
of some finite Galois extension of number fields, and `A := 𝓞K` and `B := 𝓞L` are their ring of
integers. This main result in this file implies the existence of Frobenius elements in this setting.
See `Mathlib/RingTheory/Frobenius.lean`.

## Main statements

Let `G` be a finite group acting on a commutative ring `B` satisfying `Algebra.IsInvariant A B G`.

* `Algebra.IsInvariant.isIntegral`: `B/A` is an integral extension.
* `Algebra.IsInvariant.exists_smul_of_under_eq`: `G` acts transitivity on the prime ideals of `B`
  lying above a given prime ideal of `A`.

If `Q` is a prime ideal of `B` lying over a prime ideal `P` of `A`, then

* `IsFractionRing.stabilizerHom_surjective`:
  The stabilizer subgroup of `Q` surjects onto `Aut(Frac(B/Q)/Frac(A/P))`.
* `Ideal.Quotient.stabilizerHom_surjective`:
  The stabilizer subgroup of `Q` surjects onto `Aut((B/Q)/(A/P))`.
* `Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under`:
  If `k` is a domain containing `B/Q`, then any `A/P`-algebra automorphism of `k` restricts to
  an automorphism of `B/Q`.
-/

@[expose] public section

-- this file should not import any field theory beyond the contents of `FieldTheory/Fixed.lean`
-- material involving Galois theory should be placed in `RingTheory/Invariant/Galois.lean`
assert_not_exists IntermediateField.adjoin

open scoped Pointwise

section Quotient

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

set_option backward.isDefEq.respectTransparency.types false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : Subgroup G) [H.Normal] :
    MulSemiringAction (G ⧸ H) (FixedPoints.subring B H) where
  smul := Quotient.lift (fun g x ↦ ⟨g • x, fun h ↦ by
    simpa [mul_smul] using! congr(g • $(x.2 ⟨_, ‹H.Normal›.conj_mem' _ h.2 g⟩))⟩) (by
    rintro _ a ⟨⟨⟨b⟩, hb⟩, rfl⟩
    ext c
    simpa [mul_smul] using! congr(a • $(c.2 ⟨b, hb⟩)))
  one_smul b := Subtype.ext (one_smul G b.1)
  mul_smul := Quotient.ind₂ fun _ _ _ ↦ Subtype.ext (mul_smul _ _ _)
  smul_zero := Quotient.ind fun _ ↦ Subtype.ext (smul_zero _)
  smul_add := Quotient.ind fun _ _ _ ↦ Subtype.ext (smul_add _ _ _)
  smul_one := Quotient.ind fun _ ↦ Subtype.ext (smul_one _)
  smul_mul := Quotient.ind fun _ _ _ ↦ Subtype.ext (MulSemiringAction.smul_mul _ _ _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : Subgroup G) [H.Normal] :
    MulSemiringAction (G ⧸ H) (FixedPoints.subalgebra A B H) :=
  inferInstanceAs (MulSemiringAction (G ⧸ H) (FixedPoints.subring B H))

set_option backward.isDefEq.respectTransparency.types false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : Subgroup G) [H.Normal] :
    SMulCommClass (G ⧸ H) A (FixedPoints.subalgebra A B H) where
  smul_comm := Quotient.ind fun g r h ↦ Subtype.ext (smul_comm g r h.1)

set_option backward.isDefEq.respectTransparency.types false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : Subgroup G) [H.Normal] [Algebra.IsInvariant A B G] :
    Algebra.IsInvariant A (FixedPoints.subalgebra A B H) (G ⧸ H) where
  isInvariant x hx := by
    obtain ⟨y, hy⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) x.1
      (fun g ↦ congr_arg Subtype.val (hx g))
    exact ⟨y, Subtype.ext hy⟩

end Quotient

section transitivity

variable (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B]

namespace MulSemiringAction

open Polynomial

variable {B} [Fintype G]

/-- Characteristic polynomial of a finite group action on a ring. -/
/-
**MulSemiringAction.charpoly** 是 Mathlib 中的一个定义，位于命名空间 `MulSemiringAction`。
形式化陈述：charpoly (b : B) : B[X]
参数：b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characteristic polynomial of a finite group action on a ring.
-/
noncomputable def charpoly (b : B) : B[X] := ∏ g : G, (X - C (g • b))
/-
**MulSemiringAction.charpoly_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringAction`。
形式化陈述：charpoly_eq (b : B) : charpoly G b = ∏ g : G, (X - C (g • b))
参数：b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem charpoly_eq (b : B) : charpoly G b = ∏ g : G, (X - C (g • b)) := rfl
/-
**MulSemiringAction.charpoly_eq_prod_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiring
Action`。
形式化陈述：charpoly_eq_prod_smul (b : B) : charpoly G b = ∏ g : G, g • (X - C b)
参数：b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.smul_X`：smul_X (m : M) : (m • X : R[X]) = X
· 使用定理 `Polynomial.smul_C`：smul_C {S} [SMulZeroClass S R] (s : S) (r : R) : s • 
C r = C (s • r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charpoly_eq_prod_smul (b : B) : charpoly G b = ∏ g : G, g • (X - C b) := by
  simp only [smul_sub, smul_C, smul_X, charpoly_eq]
/-
**MulSemiringAction.monic_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringAction`
。
形式化陈述：monic_charpoly (b : B) : (charpoly G b).Monic
参数：b : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_prod_of_monic`：monic_prod_of_monic (s : Finset ι) (f : 
ι -> R[X]) (hs : forall i in s, Monic (f i)) : Monic (∏ i in s, f i)
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
-/
theorem monic_charpoly (b : B) : (charpoly G b).Monic :=
  monic_prod_of_monic _ _ (fun _ _ ↦ monic_X_sub_C _)
/-
**MulSemiringAction.splits_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringAction
`。
形式化陈述：splits_charpoly (b : B) : (charpoly G b).Splits
参数：b : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.prod`：∀ {R : Type u_1} [inst : CommSemiring R] {ι : Ty
pe u_2} {f : ι → Polynomial R} {s : Finset ι},   (∀ i ∈ s, (f i).Splits) → (∏ i 
∈ s, f i).Sp…
· 使用定理 `Polynomial.Splits.X_sub_C`：∀ {R : Type u_1} [inst : Ring R] (a : R), (Po
lynomial.X - Polynomial.C a).Splits
-/
theorem splits_charpoly (b : B) : (charpoly G b).Splits :=
  .prod fun g _ ↦ .X_sub_C (g • b)
/-
**MulSemiringAction.eval_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringAction`。
形式化陈述：eval_charpoly (b : B) : (charpoly G b).eval b = 0
参数：b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulSemiringAction.charpoly_eq`：charpoly_eq (b : B) : charpoly G b = ∏ g 
: G, (X - C (g • b))
· 使用定理 `Polynomial.eval_prod`：eval_prod {ι : Type*} (s : Finset ι) (p : ι -> R[X
]) (x : R) : eval x (∏ j in s, p j) = ∏ j in s, eval x (p j)
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem eval_charpoly (b : B) : (charpoly G b).eval b = 0 := by
  rw [charpoly_eq, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
  rw [one_smul, eval_sub, eval_C, eval_X, sub_self]

variable {G}
/-
**MulSemiringAction.smul_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringAction`。
形式化陈述：smul_charpoly (b : B) (g : G) : g • (charpoly G b) = charpoly G b
参数：b : B；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulSemiringAction.charpoly_eq_prod_smul`：charpoly_eq_prod_smul (b : B) :
 charpoly G b = ∏ g : G, g • (X - C b)
· 使用定理 `Finset.smul_prod_perm`：Finset.smul_prod_perm [Fintype G] (b : N) (g : G)
 : (g • ∏ h : G, h • b) = ∏ h : G, h • b
-/
theorem smul_charpoly (b : B) (g : G) : g • (charpoly G b) = charpoly G b := by
  rw [charpoly_eq_prod_smul, Finset.smul_prod_perm]
/-
**MulSemiringAction.smul_coeff_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringAc
tion`。
形式化陈述：smul_coeff_charpoly (b : B) (n : Nat) (g : G) : g • (charpoly G b).coeff n
 = (charpoly G b).coeff n
参数：b : B；n : Nat；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `MulSemiringAction.smul_charpoly`：smul_charpoly (b : B) (g : G) : g • (ch
arpoly G b) = charpoly G b
-/
theorem smul_coeff_charpoly (b : B) (n : ℕ) (g : G) :
    g • (charpoly G b).coeff n = (charpoly G b).coeff n := by
  rw [← coeff_smul, smul_charpoly]

end MulSemiringAction

namespace Algebra.IsInvariant

open MulSemiringAction Polynomial

variable [IsInvariant A B G]

/-
**Algebra.IsInvariant.charpoly_mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsIn
variant`。
形式化陈述：charpoly_mem_lifts [Fintype G] (b : B) : charpoly G b in Polynomial.lifts 
(algebraMap A B)
参数：b : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.lifts_iff_coeff_lifts`：lifts_iff_coeff_lifts (p : S[X]) : p i
n lifts f ↔ forall n : Nat, p.coeff n in Set.range f
· 使用定理 `Algebra.IsInvariant.isInvariant`：∀ {A : Type u_1} {B : Type u_2} {G : Ty
pe u_3} {inst : CommSemiring A} {inst_1 : Semiring B} {inst_2 : Algebra A B}   {
inst_3 : Group G} {in…
· 使用定理 `MulSemiringAction.smul_coeff_charpoly`：smul_coeff_charpoly (b : B) (n : 
Nat) (g : G) : g • (charpoly G b).coeff n = (charpoly G b).coeff n
-/
theorem charpoly_mem_lifts [Fintype G] (b : B) :
    charpoly G b ∈ Polynomial.lifts (algebraMap A B) :=
  (charpoly G b).lifts_iff_coeff_lifts.mpr fun n ↦ isInvariant _ (smul_coeff_charpoly b n)
/-
**Algebra.IsInvariant.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsInvariant`
。
形式化陈述：isIntegral [Finite G] : Algebra.IsIntegral A B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `MulSemiringAction.eval_charpoly`：eval_charpoly (b : B) : (charpoly G b).
eval b = 0
-/
theorem isIntegral [Finite G] : Algebra.IsIntegral A B := by
  cases nonempty_fintype G
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨p, hp1, -, hp2⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (charpoly_mem_lifts A B G b) (monic_charpoly G b)
  exact ⟨p, hp2, by rw [← eval_map, hp1, eval_charpoly]⟩

/-- `G` acts transitively on the prime ideals of `B` above a given prime ideal of `A`. -/
/-
**Algebra.IsInvariant.exists_smul_of_under_eq** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.IsInvariant`。
形式化陈述：exists_smul_of_under_eq [Finite G] [SMulCommClass G A B] (P Q : Ideal B) [
hP : P.IsPrime] [hQ : Q.IsPrime] (hPQ : P.under A = Q.under A) : exists g : G, Q
 = g • P
参数：P Q : Ideal B；hPQ : P.under A = Q.under A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.subset_union_prime`：subset_union_prime {R : Type u} [CommRing R] {
s : Finset ι} {f : ι -> Ideal R} (a b : ι) (hp : forall i in s, i != a -> i != b
 -> IsPrime (f…
· 使用定理 `Ideal.IsPrime.smul`：∀ {M : Type u_1} {R : Type u_3} [inst : Group M] [in
st_1 : Semiring R] [inst_2 : MulSemiringAction M R] {I : Ideal R}   [H : I.IsPri
me] (g :…
· 使用定理 `Algebra.IsInvariant.isInvariant`：∀ {A : Type u_1} {B : Type u_2} {G : Ty
pe u_3} {inst : CommSemiring A} {inst_1 : Semiring B} {inst_2 : Algebra A B}   {
inst_3 : Group G} {in…
· 使用定理 `Finset.smul_prod_perm`：Finset.smul_prod_perm [Fintype G] (b : N) (g : G)
 : (g • ∏ h : G, h • b) = ∏ h : G, h • b
· 使用定理 `Ideal.IsPrime.prod_mem_iff`：∀ {R : Type u} {ι : Type u_1} [inst : CommSe
miring R] {s : Finset ι} {x : ι → R} {p : Ideal R} [hp : p.IsPrime],   ∏ i ∈ s, 
x i ∈ p ↔ ∃ i ∈ …
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.mem_inv_pointwise_smul_iff`：mem_inv_pointwise_smul_iff {a : M} {S 
: Ideal R} {x : R} : x in a⁻¹ • S ↔ a • x in S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Ideal.under_smul`：under_smul [SMulCommClass G A B] : (g • P : Ideal B).u
nder A = P.under A
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `smul_eq_of_le_smul`：smul_eq_of_le_smul {G : Type*} [Group G] [Finite G] 
{α : Type*} [PartialOrder α] {g : G} {a : α} [MulAction G α] [CovariantClass G α
 HSMul.h…
· 使用定理 `Ideal.instCovariantClassHSMulLe`：∀ {M : Type u_1} {R : Type u_3} [inst :
 Monoid M] [inst_1 : Semiring R] [inst_2 : MulSemiringAction M R],   CovariantCl
ass M (Ideal R) HSMul…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
`G` acts transitively on the prime ideals of `B` above a given prime ideal of `A
`.
-/
theorem exists_smul_of_under_eq [Finite G] [SMulCommClass G A B]
    (P Q : Ideal B) [hP : P.IsPrime] [hQ : Q.IsPrime]
    (hPQ : P.under A = Q.under A) :
    ∃ g : G, Q = g • P := by
  cases nonempty_fintype G
  have : ∀ (P Q : Ideal B) [P.IsPrime] [Q.IsPrime], P.under A = Q.under A →
      ∃ g ∈ (⊤ : Finset G), Q ≤ g • P := by
    intro P Q hP hQ hPQ
    rw [← Ideal.subset_union_prime 1 1 (fun _ _ _ _ ↦ hP.smul _)]
    intro b hb
    suffices h : ∃ g ∈ Finset.univ, g • b ∈ P by
      obtain ⟨g, -, hg⟩ := h
      apply Set.mem_biUnion (Finset.mem_univ g⁻¹) (Ideal.mem_inv_pointwise_smul_iff.mpr hg)
    obtain ⟨a, ha⟩ := isInvariant (A := A) (∏ g : G, g • b) (Finset.smul_prod_perm b)
    rw [← hP.prod_mem_iff, ← ha, ← P.mem_comap, ← P.under_def A,
      hPQ, Q.mem_comap, ha, hQ.prod_mem_iff]
    exact ⟨1, Finset.mem_univ 1, (one_smul G b).symm ▸ hb⟩
  obtain ⟨g, -, hg⟩ := this P Q hPQ
  obtain ⟨g', -, hg'⟩ := this Q (g • P) ((P.under_smul A g).trans hPQ).symm
  exact ⟨g, le_antisymm hg (smul_eq_of_le_smul (hg.trans hg') ▸ hg')⟩
/-
**Algebra.IsInvariant.orbit_eq_primesOver** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsI
nvariant`。
形式化陈述：orbit_eq_primesOver [Finite G] [SMulCommClass G A B] (P : Ideal A) (Q : Id
eal B) [hP : Q.LiesOver P] [hQ : Q.IsPrime] : MulAction.orbit G Q = P.primesOver
 B
参数：P : Ideal A；Q : Ideal B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ideal.IsPrime.smul`：∀ {M : Type u_1} {R : Type u_3} [inst : Group M] [in
st_1 : Semiring R] [inst_2 : MulSemiringAction M R] {I : Ideal R}   [H : I.IsPri
me] (g :…
· 使用定理 `Ideal.LiesOver.smul`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] {P : Ideal B}   {p : Ideal A} 
{G : Type…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Algebra.IsInvariant.exists_smul_of_under_eq`：exists_smul_of_under_eq [Fi
nite G] [SMulCommClass G A B] (P Q : Ideal B) [hP : P.IsPrime] [hQ : Q.IsPrime] 
(hPQ : P.under A = Q.under A) : e…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem orbit_eq_primesOver [Finite G] [SMulCommClass G A B] (P : Ideal A) (Q : Ideal B)
    [hP : Q.LiesOver P] [hQ : Q.IsPrime] : MulAction.orbit G Q = P.primesOver B := by
  refine Set.ext fun R ↦ ⟨fun ⟨g, hg⟩ ↦ hg ▸ ⟨hQ.smul g, hP.smul g⟩, fun h ↦ ?_⟩
  have : R.IsPrime := h.1
  obtain ⟨g, hg⟩ := exists_smul_of_under_eq A B G Q R (hP.over.symm.trans h.2.over)
  exact ⟨g, hg.symm⟩

end Algebra.IsInvariant

end transitivity

section surjectivity

open FaithfulSMul IsScalarTower Polynomial

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]

variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [Algebra (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]
  [Algebra.IsInvariant A B G]

/-- A technical lemma for `fixed_of_fixed1`. -/
/-
**fixed_of_fixed1_aux1** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A technical lemma for `fixed_of_fixed1`.
-/
private theorem fixed_of_fixed1_aux1 :
    ∃ a b : B, (∀ g : G, g • a = a) ∧ a ∉ Q ∧
    ∀ g : G, algebraMap B (B ⧸ Q) (g • b) = algebraMap B (B ⧸ Q) (if g • Q = Q then a else 0) := by
  obtain ⟨_⟩ := nonempty_fintype G
  let P := Finset.inf {g : G | g • Q ≠ Q} (fun g ↦ g • Q)
  have h1 : ¬ P ≤ Q := by
    rw [Ideal.IsPrime.inf_le' inferInstance]
    rintro ⟨g, hg1, hg2⟩
    exact (Finset.mem_filter.mp hg1).2 (smul_eq_of_smul_le hg2)
  obtain ⟨b, hbP, hbQ⟩ := SetLike.not_le_iff_exists.mp h1
  replace hbP : ∀ g : G, g • Q ≠ Q → b ∈ g • Q :=
    fun g hg ↦ (Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩) : P ≤ g • Q) hbP
  let f := MulSemiringAction.charpoly G b
  obtain ⟨q, hq, hq0⟩ :=
    (f.map (algebraMap B (B ⧸ Q))).exists_eq_pow_rootMultiplicity_mul_and_not_dvd
      (Polynomial.map_monic_ne_zero (MulSemiringAction.monic_charpoly G b)) 0
  rw [map_zero, sub_zero] at hq hq0
  let j := (f.map (algebraMap B (B ⧸ Q))).rootMultiplicity 0
  let k := q.natDegree
  let r := ∑ i ∈ Finset.range (k + 1), Polynomial.monomial i (f.coeff (i + j))
  have hr : r.map (algebraMap B (B ⧸ Q)) = q := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range_succ_iff]
    split_ifs with hn
    · rw [← Polynomial.coeff_map, hq, Polynomial.coeff_X_pow_mul]
    · rw [map_zero, eq_comm, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn)]
  have hf : f.eval b = 0 := MulSemiringAction.eval_charpoly G b
  have hr : r.eval b ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq] at hbQ ⊢
    replace hf := congrArg (algebraMap B (B ⧸ Q)) hf
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map] at hf ⊢
    rwa [map_zero, hq, ← hr, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      mul_eq_zero, or_iff_right (pow_ne_zero _ hbQ)] at hf
  let a := f.coeff j
  have ha : ∀ g : G, g • a = a := MulSemiringAction.smul_coeff_charpoly b j
  have hr' : ∀ g : G, g • Q ≠ Q → a - r.eval b ∈ g • Q := by
    intro g hg
    have hr : r = ∑ i ∈ Finset.range (k + 1), Polynomial.monomial i (f.coeff (i + j)) := rfl
    rw [← Ideal.neg_mem_iff, neg_sub, hr, Finset.sum_range_succ', Polynomial.eval_add,
        Polynomial.eval_monomial, zero_add, pow_zero, mul_one, add_sub_cancel_right]
    simp only [← Polynomial.monomial_mul_X]
    rw [← Finset.sum_mul, Polynomial.eval_mul_X]
    exact Ideal.mul_mem_left (g • Q) _ (hbP g hg)
  refine ⟨a, a - r.eval b, ha, ?_, fun h ↦ ?_⟩
  · rwa [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq, ← Polynomial.coeff_map,
      ← zero_add j, hq, Polynomial.coeff_X_pow_mul, ← Polynomial.X_dvd_iff]
  · rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
      ← Ideal.smul_mem_pointwise_smul_iff (a := h⁻¹), smul_sub, inv_smul_smul]
    simp only [← eq_inv_smul_iff (g := h), eq_comm (a := Q)]
    split_ifs with hh
    · rwa [ha, sub_sub_cancel_left, hh, Q.neg_mem_iff]
    · rw [smul_zero, sub_zero]
      exact hr' h⁻¹ hh

/-- A technical lemma for `fixed_of_fixed1`. -/
/-
**fixed_of_fixed1_aux2** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A technical lemma for `fixed_of_fixed1`.
-/
private theorem fixed_of_fixed1_aux2 (b₀ : B)
    (hx : ∀ g : G, g • Q = Q → algebraMap B (B ⧸ Q) (g • b₀) = algebraMap B (B ⧸ Q) b₀) :
    ∃ a b : B, (∀ g : G, g • a = a) ∧ a ∉ Q ∧
    (∀ g : G, algebraMap B (B ⧸ Q) (g • b) =
      algebraMap B (B ⧸ Q) (if g • Q = Q then a * b₀ else 0)) := by
  obtain ⟨a, b, ha1, ha2, hb⟩ := fixed_of_fixed1_aux1 G Q
  refine ⟨a, b * b₀, ha1, ha2, fun g ↦ ?_⟩
  rw [smul_mul', map_mul, hb]
  specialize hb g
  split_ifs with hg
  · rw [map_mul, hx g hg]
  · rw [map_zero, zero_mul]

/-- A technical lemma for `fixed_of_fixed1`. -/
/-
**fixed_of_fixed1_aux3** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A technical lemma for `fixed_of_fixed1`.
-/
private theorem fixed_of_fixed1_aux3 [NoZeroDivisors B] {b : B} {i j : ℕ} {p : Polynomial A}
    (h : p.map (algebraMap A B) = (X - C b) ^ i * X ^ j) (f : B ≃ₐ[A] B) (hi : i ≠ 0) :
    f b = b := by
  by_cases ha : b = 0
  · rw [ha, map_zero]
  have hf := congrArg (eval b) (congrArg (Polynomial.mapAlgHom f.toAlgHom) h)
  rw [coe_mapAlgHom, map_map, f.toAlgHom.comp_algebraMap, h] at hf
  simp_rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C,
    eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow hi, zero_mul,
    zero_eq_mul, or_iff_left (pow_ne_zero j ha), pow_eq_zero_iff hi, sub_eq_zero] at hf
  exact hf.symm

/-- This theorem will be made redundant by `IsFractionRing.stabilizerHom_surjective`. -/
/-
**fixed_of_fixed1** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This theorem will be made redundant by `IsFractionRing.stabilizerHom_surjective`
.
-/
private theorem fixed_of_fixed1 [Module.IsTorsionFree (B ⧸ Q) L] (f : Gal(L/K)) (b : B ⧸ Q)
    (hx : ∀ g : MulAction.stabilizer G Q, Ideal.Quotient.stabilizerHom Q P G g b = b) :
    f (algebraMap (B ⧸ Q) L b) = (algebraMap (B ⧸ Q) L b) := by
  cases nonempty_fintype G
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← Ideal.Quotient.algebraMap_eq]
  obtain ⟨a, b, ha1, ha2, hb⟩ := fixed_of_fixed1_aux2 G Q b₀ (fun g hg ↦ hx ⟨g, hg⟩)
  obtain ⟨M, key⟩ := (mem_lifts _).mp (Algebra.IsInvariant.charpoly_mem_lifts A B G b)
  replace key := congrArg (map (algebraMap B (B ⧸ Q))) key
  rw [map_map, ← algebraMap_eq, algebraMap_eq A (A ⧸ P) (B ⧸ Q),
      ← map_map, MulSemiringAction.charpoly, Polynomial.map_prod] at key
  have key₀ : ∀ g : G, (X - C (g • b)).map (algebraMap B (B ⧸ Q)) =
      if g • Q = Q then X - C (algebraMap B (B ⧸ Q) (a * b₀)) else X := by
    intro g
    rw [Polynomial.map_sub, map_X, map_C, hb]
    split_ifs
    · rfl
    · rw [map_zero, map_zero, sub_zero]
  simp only [key₀, Finset.prod_ite, Finset.prod_const] at key
  replace key := congrArg (map (algebraMap (B ⧸ Q) L)) key
  rw [map_map, ← algebraMap_eq, algebraMap_eq (A ⧸ P) K L,
      ← map_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_sub,
      map_X, map_C] at key
  replace key := fixed_of_fixed1_aux3 key f (Finset.card_ne_zero_of_mem
    (Finset.mem_filter.mpr ⟨Finset.mem_univ 1, one_smul G Q⟩))
  simp only [map_mul] at key
  obtain ⟨a, rfl⟩ := Algebra.IsInvariant.isInvariant (A := A) a ha1
  rwa [← algebraMap_apply A B (B ⧸ Q), algebraMap_apply A (A ⧸ P) (B ⧸ Q),
      ← algebraMap_apply, algebraMap_apply (A ⧸ P) K L, f.commutes, mul_right_inj'] at key
  rwa [← algebraMap_apply, algebraMap_apply (A ⧸ P) (B ⧸ Q) L,
      ← algebraMap_apply A (A ⧸ P) (B ⧸ Q), algebraMap_apply A B (B ⧸ Q),
      Ne, algebraMap_eq_zero_iff, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]

variable [IsFractionRing (A ⧸ P) K] [IsFractionRing (B ⧸ Q) L]

/-- If `Q` lies over `P`, then the stabilizer of `Q` acts on `Frac(B/Q)/Frac(A/P)`. -/
/-
**IsFractionRing.stabilizerHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsFractionRing.stabilizerHom : MulAction.stabilizer G Q ->* Gal(L/K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Q` lies over `P`, then the stabilizer of `Q` acts on `Frac(B/Q)/Frac(A/P)`.
-/
noncomputable def IsFractionRing.stabilizerHom : MulAction.stabilizer G Q →* Gal(L/K) :=
  MonoidHom.comp (IsFractionRing.fieldEquivOfAlgEquivHom K L) (Ideal.Quotient.stabilizerHom Q P G)

omit [Finite G] [Q.IsPrime] [Algebra.IsInvariant A B G] in
@[simp]
/-
**IsFractionRing.stabilizerHom_apply_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsFractionRing.stabilizerHom_apply_apply_mk (σ : MulAction.stabilizer G Q)
 (x : B) : IsFractionRing.stabilizerHom G P Q K L σ (algebraMap _ L (Ideal.Quoti
ent.mk Q x)) = algebraMap _ L (Ideal.Quotient.mk Q (σ.val • x))
参数：σ : MulAction.stabilizer G Q；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsFractionRing.fieldEquivOfAlgEquiv_algebraMap`：fieldEquivOfAlgEquiv_alg
ebraMap (f : B ≃ₐ[A] C) (b : B) : fieldEquivOfAlgEquiv FA FB FC f (algebraMap B 
FB b) = algebraMap C FC (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsFractionRing.stabilizerHom_apply_apply_mk (σ : MulAction.stabilizer G Q) (x : B) :
    IsFractionRing.stabilizerHom G P Q K L σ (algebraMap _ L (Ideal.Quotient.mk Q x)) =
      algebraMap _ L (Ideal.Quotient.mk Q (σ.val • x)) := by
  simp [IsFractionRing.stabilizerHom, MulAction.subgroup_smul_def]

omit [Finite G] [Q.IsPrime] [Algebra.IsInvariant A B G] in
/-
**IsFractionRing.ker_stabilizerHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsFractionRing.ker_stabilizerHom : (stabilizerHom G P Q K L).ker = Q.inert
ia (MulAction.stabilizer G Q)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.stabilizerHom.eq_1`：∀ {A : Type u_1} {B : Type u_2} [inst
 : CommRing A] [inst_1 : CommRing B] [inst_2 : Algebra A B] (G : Type u_3)   [in
st_3 : Group G] [inst_4…
· 使用引理 `MonoidHom.ker_comp_of_injective`：ker_comp_of_injective {P : Type*} [MulO
neClass P] (f : G ->* N) (g : N ->* P) (hg : Function.Injective g) : (g.comp f).
ker = f.ker
· 使用引理 `IsFractionRing.fieldEquivOfAlgEquivHom_injective`：fieldEquivOfAlgEquivHo
m_injective : Function.Injective (fieldEquivOfAlgEquivHom K L : (B ≃ₐ[A] B) ->* 
(L ≃ₐ[K] L))
· 使用引理 `Ideal.Quotient.ker_stabilizerHom`：ker_stabilizerHom : (stabilizerHom P p
 G).ker = P.inertia (MulAction.stabilizer G P)
-/
theorem IsFractionRing.ker_stabilizerHom :
    (stabilizerHom G P Q K L).ker = Q.inertia (MulAction.stabilizer G Q) := by
  rw [stabilizerHom, MonoidHom.ker_comp_of_injective, Ideal.Quotient.ker_stabilizerHom]
  apply fieldEquivOfAlgEquivHom_injective

/-- This theorem will be made redundant by `IsFractionRing.stabilizerHom_surjective`. -/
/-
**fixed_of_fixed2** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This theorem will be made redundant by `IsFractionRing.stabilizerHom_surjective`
.
-/
private theorem fixed_of_fixed2 (f : Gal(L/K)) (x : L)
    (hx : ∀ g : MulAction.stabilizer G Q, IsFractionRing.stabilizerHom G P Q K L g x = x) :
    f x = x := by
  obtain ⟨_⟩ := nonempty_fintype G
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (B ⧸ Q) x
  obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A ⧸ P) y).exists_smul_eq_mul x hy
  replace ha : algebraMap (A ⧸ P) L a ≠ 0 := by
    rwa [Ne, algebraMap_apply (A ⧸ P) K L, algebraMap_eq_zero_iff, algebraMap_eq_zero_iff]
  replace hy : algebraMap (B ⧸ Q) L y ≠ 0 :=
    mt (algebraMap_eq_zero_iff (B ⧸ Q) L).mp (nonZeroDivisors.ne_zero hy)
  replace h : algebraMap (B ⧸ Q) L x / algebraMap (B ⧸ Q) L y =
      algebraMap (B ⧸ Q) L b / algebraMap (A ⧸ P) L a := by
    rw [mul_comm, Algebra.smul_def, mul_comm] at h
    rw [div_eq_div_iff hy ha, ← map_mul, ← h, map_mul, ← algebraMap_apply]
  simp only [h, map_div₀, algebraMap_apply (A ⧸ P) K L, AlgEquiv.commutes] at hx ⊢
  simp only [← algebraMap_apply, div_left_inj' ha] at hx ⊢
  exact fixed_of_fixed1 G P Q K L f b (fun g ↦ IsFractionRing.injective (B ⧸ Q) L
    ((IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K L L
      (Ideal.Quotient.stabilizerHom Q P G g) b).symm.trans (hx g)))

/-- The stabilizer subgroup of `Q` surjects onto `Aut(Frac(B/Q)/Frac(A/P))`. -/
/-
**IsFractionRing.stabilizerHom_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsFractionRing.stabilizerHom_surjective : Function.Surjective (stabilizerH
om G P Q K L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `FixedPoints.instSMulCommClassSubtypeMemSubfieldSubfield`：∀ (M : Type u) 
[inst : Monoid M] (F : Type v) [inst_1 : Field F] [inst_2 : MulSemiringAction M 
F],   SMulCommClass M (↥(FixedPoints.subfield…
· 使用定理 `_private.Mathlib.RingTheory.Invariant.Basic.0.fixed_of_fixed2`：∀ {A : Ty
pe u_1} {B : Type u_2} [inst : CommRing A] [inst_1 : CommRing B] [inst_2 : Algeb
ra A B] (G : Type u_3)   [inst_3 : Group G] [Finite…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `FixedPoints.toAlgAut_surjective`：toAlgAut_surjective [Finite G] : Functi
on.Surjective (MulSemiringAction.toAlgAut G (FixedPoints.subfield G F) F)
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ext_iff`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst 
: CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Alge
bra R …

--- 原说明 ---
The stabilizer subgroup of `Q` surjects onto `Aut(Frac(B/Q)/Frac(A/P))`.
-/
theorem IsFractionRing.stabilizerHom_surjective :
    Function.Surjective (stabilizerHom G P Q K L) := by
  let _ := MulSemiringAction.compHom L (stabilizerHom G P Q K L)
  intro f
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective (MulAction.stabilizer G Q) L
    (AlgEquiv.ofRingEquiv (f := f) (fun x ↦ fixed_of_fixed2 G P Q K L f x x.2))
  exact ⟨g, by rwa [AlgEquiv.ext_iff] at hg ⊢⟩

/-- The stabilizer subgroup of `Q` surjects onto `Aut((B/Q)/(A/P))`. -/
/-
**Ideal.Quotient.stabilizerHom_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.Quotient.stabilizerHom_surjective : Function.Surjective (Ideal.Quoti
ent.stabilizerHom Q P G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsFractionRing.stabilizerHom_surjective`：IsFractionRing.stabilizerHom_su
rjective : Function.Surjective (stabilizerHom G P Q K L)
· 使用定理 `Function.Surjective.of_comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : S
ort u_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Injec
tive f → Function.Surj…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.coe_comp`：MonoidHom.coe_comp [MulOne M] [MulOne N] [MulOne P] 
(g : N ->* P) (f : M ->* N) : ↑(g.comp f) = g ∘ f
· 使用定理 `IsFractionRing.stabilizerHom.eq_1`：∀ {A : Type u_1} {B : Type u_2} [inst
 : CommRing A] [inst_1 : CommRing B] [inst_2 : Algebra A B] (G : Type u_3)   [in
st_3 : Group G] [inst_4…
· 使用引理 `IsFractionRing.fieldEquivOfAlgEquivHom_injective`：fieldEquivOfAlgEquivHo
m_injective : Function.Injective (fieldEquivOfAlgEquivHom K L : (B ≃ₐ[A] B) ->* 
(L ≃ₐ[K] L))

--- 原说明 ---
The stabilizer subgroup of `Q` surjects onto `Aut((B/Q)/(A/P))`.
-/
theorem Ideal.Quotient.stabilizerHom_surjective :
    Function.Surjective (Ideal.Quotient.stabilizerHom Q P G) := by
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
  let _ := FractionRing.liftAlgebra (A ⧸ P) (FractionRing (B ⧸ Q))
  have key := IsFractionRing.stabilizerHom_surjective G P Q
    (FractionRing (A ⧸ P)) (FractionRing (B ⧸ Q))
  rw [IsFractionRing.stabilizerHom, MonoidHom.coe_comp] at key
  exact key.of_comp_left (IsFractionRing.fieldEquivOfAlgEquivHom_injective (A ⧸ P) (B ⧸ Q)
    (FractionRing (A ⧸ P)) (FractionRing (B ⧸ Q)))

/--
The isomorphism between `stabilizer G Q ⧸ inertia G Q` and the Galois group of the residue fields.
-/
/-
**IsFractionRing.stabilizerQuotientInertiaEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsFractionRing.stabilizerQuotientInertiaEquiv : MulAction.stabilizer G Q ⧸
 Q.inertia (MulAction.stabilizer G Q) ≃* Gal(L/K)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.stabilizerHom_surjective`：IsFractionRing.stabilizerHom_su
rjective : Function.Surjective (stabilizerHom G P Q K L)

--- 原说明 ---
The isomorphism between `stabilizer G Q ⧸ inertia G Q` and the Galois group of t
he residue fields.
-/
noncomputable def IsFractionRing.stabilizerQuotientInertiaEquiv :
    MulAction.stabilizer G Q ⧸ Q.inertia (MulAction.stabilizer G Q) ≃* Gal(L/K) :=
  QuotientGroup.liftEquiv (N := Q.inertia (MulAction.stabilizer G Q))
    (stabilizerHom_surjective G P Q K L) (ker_stabilizerHom G P Q K L).symm

@[simp]
/-
**IsFractionRing.stabilizerQuotientInertiaEquiv_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsFractionRing.stabilizerQuotientInertiaEquiv_mk (g : MulAction.stabilizer
 G Q) : stabilizerQuotientInertiaEquiv G P Q K L g = stabilizerHom G P Q K L g
参数：g : MulAction.stabilizer G Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instNormalSubtypeMemSubgroupStabilizerInertia`：∀ {M : Type u_1} [i
nst : Group M] {R : Type u_4} [inst_1 : Ring R] (P : Ideal R) [inst_2 : MulSemir
ingAction M R],   (Ideal.inertia (↥(MulAc…
-/
theorem IsFractionRing.stabilizerQuotientInertiaEquiv_mk (g : MulAction.stabilizer G Q) :
    stabilizerQuotientInertiaEquiv G P Q K L g = stabilizerHom G P Q K L g := rfl

/--
The isomorphism between `stabilizer G Q ⧸ inertia G Q` and the Galois group of the residue fields
extension `B ⧸ Q` over `A ⧸ P`.
-/
/-
**Ideal.Quotient.stabilizerQuotientInertiaEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.Quotient.stabilizerQuotientInertiaEquiv : MulAction.stabilizer G Q ⧸
 Q.inertia (MulAction.stabilizer G Q) ≃* Gal((B ⧸ Q)/(A ⧸ P))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.stabilizerHom_surjective`：Ideal.Quotient.stabilizerHom_su
rjective : Function.Surjective (Ideal.Quotient.stabilizerHom Q P G)

--- 原说明 ---
The isomorphism between `stabilizer G Q ⧸ inertia G Q` and the Galois group of t
he residue fields
extension `B ⧸ Q` over `A ⧸ P`.
-/
noncomputable def Ideal.Quotient.stabilizerQuotientInertiaEquiv :
    MulAction.stabilizer G Q ⧸ Q.inertia (MulAction.stabilizer G Q) ≃*
      Gal((B ⧸ Q)/(A ⧸ P)) :=
  QuotientGroup.liftEquiv (N := Q.inertia (MulAction.stabilizer G Q))
    (stabilizerHom_surjective G P Q) (ker_stabilizerHom Q P G).symm

@[simp]
/-
**Ideal.Quotient.stabilizerQuotientInertiaEquiv_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.Quotient.stabilizerQuotientInertiaEquiv_mk (g : MulAction.stabilizer
 G Q) : stabilizerQuotientInertiaEquiv G P Q g = stabilizerHom Q P G g
参数：g : MulAction.stabilizer G Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instNormalSubtypeMemSubgroupStabilizerInertia`：∀ {M : Type u_1} [i
nst : Group M] {R : Type u_4} [inst_1 : Ring R] (P : Ideal R) [inst_2 : MulSemir
ingAction M R],   (Ideal.inertia (↥(MulAc…
-/
theorem Ideal.Quotient.stabilizerQuotientInertiaEquiv_mk (g : MulAction.stabilizer G Q) :
    stabilizerQuotientInertiaEquiv G P Q g = stabilizerHom Q P G g := rfl

end surjectivity

section normal

variable {A B k : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Finite G] [Group G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]
  [CommRing k] [Algebra (A ⧸ P) k] [Algebra (B ⧸ Q) k] [IsScalarTower (A ⧸ P) (B ⧸ Q) k]
  [IsDomain k] [FaithfulSMul (B ⧸ Q) k]

include G in
/--
For any domain `k` containing `B ⧸ Q`,
any endomorphism of `k` can be restricted to an endomorphism of `B ⧸ Q`.

This is basically the fact that `L/K` normal implies `κ(Q)/κ(P)` normal in the Galois setting.
-/
/-
**Ideal.Quotient.exists_algHom_fixedPoint_quotient_under** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：Ideal.Quotient.exists_algHom_fixedPoint_quotient_under (σ : k ->ₐ[A ⧸ P] k
) : exists τ : (B ⧸ Q) ->ₐ[A ⧸ P] B ⧸ Q, forall x : B ⧸ Q, algebraMap _ _ (τ x) 
= σ (algebraMap (B ⧸ Q) k x)
参数：σ : k ->ₐ[A ⧸ P] k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `Algebra.IsInvariant.charpoly_mem_lifts`：charpoly_mem_lifts [Fintype G] (
b : B) : charpoly G b in Polynomial.lifts (algebraMap A B)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Polynomial.coe_mapRingHom`：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom 
f) = map f
· 使用定理 `MulSemiringAction.eval_charpoly`：eval_charpoly (b : B) : (charpoly G b).
eval b = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Polynomial.aeval_algHom`：aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (
f x) = f.comp (aeval x)
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
· 使用定理 `Ideal.Quotient.algebraMap_eq`：∀ {R : Type u_5} [inst : CommRing R] (I : 
Ideal R), algebraMap R (R ⧸ I) = Ideal.Quotient.mk I
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
For any domain `k` containing `B ⧸ Q`,
any endomorphism of `k` can be restricted to an endomorphism of `B ⧸ Q`.

This is basically the fact that `L/K` normal implies `κ(Q)/κ(P)` normal in the G
alois setting.
-/
lemma Ideal.Quotient.exists_algHom_fixedPoint_quotient_under
    (σ : k →ₐ[A ⧸ P] k) :
    ∃ τ : (B ⧸ Q) →ₐ[A ⧸ P] B ⧸ Q, ∀ x : B ⧸ Q,
      algebraMap _ _ (τ x) = σ (algebraMap (B ⧸ Q) k x) := by
  let f : (B ⧸ Q) →ₐ[A ⧸ P] k := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  suffices (σ.comp f).range ≤ f.range by
    let e := (AlgEquiv.ofInjective f hf)
    exact ⟨(e.symm.toAlgHom.comp (Subalgebra.inclusion this)).comp (σ.comp f).rangeRestrict,
      fun x ↦ congr_arg Subtype.val (e.apply_symm_apply ⟨_, _⟩)⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  cases nonempty_fintype G
  algebraize [(algebraMap (A ⧸ P) k).comp (algebraMap A (A ⧸ P)),
    (algebraMap (B ⧸ Q) k).comp (algebraMap B (B ⧸ Q))]
  have : IsScalarTower A (B ⧸ Q) k := .of_algebraMap_eq fun x ↦
    (IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) k (mk P x))
  have : IsScalarTower A B k := .of_algebraMap_eq fun x ↦
    (IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) k (mk P x))
  obtain ⟨P, hp⟩ := Algebra.IsInvariant.charpoly_mem_lifts A B G x
  have : Polynomial.aeval x P = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map,
      ← Polynomial.coe_mapRingHom (R := A), hp, MulSemiringAction.eval_charpoly]
  have : Polynomial.aeval (σ (algebraMap (B ⧸ Q) k (mk _ x))) P = 0 := by
    refine (DFunLike.congr_fun (Polynomial.aeval_algHom ((σ.restrictScalars A).comp
      (IsScalarTower.toAlgHom A (B ⧸ Q) k)) _) P).trans ?_
    rw [AlgHom.comp_apply, ← algebraMap_eq, Polynomial.aeval_algebraMap_apply, this,
      map_zero, map_zero]
  rw [← Polynomial.aeval_map_algebraMap B, ← Polynomial.coe_mapRingHom, hp] at this
  obtain ⟨τ, hτ⟩ : ∃ τ : G, σ (algebraMap _ _ x) = algebraMap _ _ (τ • x) := by
    simpa [MulSemiringAction.charpoly, sub_eq_zero, Finset.prod_eq_zero_iff] using! this
  exact ⟨Ideal.Quotient.mk _ (τ • x), hτ.symm⟩

include G in
/--
For any domain `k` containing `B ⧸ Q`,
any endomorphism of `k` can be restricted to an endomorphism of `B ⧸ Q`.
-/
/-
**Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under (σ : k ≃ₐ[A ⧸ P] 
k) : exists τ : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q, forall x : B ⧸ Q, algebraMap _ _ (τ x) 
= σ (algebraMap (B ⧸ Q) k x)
参数：σ : k ≃ₐ[A ⧸ P] k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用引理 `Ideal.Quotient.exists_algHom_fixedPoint_quotient_under`：Ideal.Quotient.e
xists_algHom_fixedPoint_quotient_under (σ : k ->ₐ[A ⧸ P] k) : exists τ : (B ⧸ Q)
 ->ₐ[A ⧸ P] B ⧸ Q, forall x : B ⧸ Q, algebra…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `RingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemiri
ng α] [inst_1 : NonAssocSemiring β] (self : α →+* β) (x y : α),   (↑↑self).toFun
 (x + …
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…

--- 原说明 ---
For any domain `k` containing `B ⧸ Q`,
any endomorphism of `k` can be restricted to an endomorphism of `B ⧸ Q`.
-/
lemma Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under
    (σ : k ≃ₐ[A ⧸ P] k) :
    ∃ τ : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q, ∀ x : B ⧸ Q,
      algebraMap _ _ (τ x) = σ (algebraMap (B ⧸ Q) k x) := by
  let f : (B ⧸ Q) →ₐ[A ⧸ P] k := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨τ₁, h₁⟩ := Ideal.Quotient.exists_algHom_fixedPoint_quotient_under G P Q σ.toAlgHom
  obtain ⟨τ₂, h₂⟩ := Ideal.Quotient.exists_algHom_fixedPoint_quotient_under G P Q σ.symm.toAlgHom
  refine ⟨{ __ := τ₁, invFun := τ₂, left_inv := ?_, right_inv := ?_ }, h₁⟩
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, e⟩ := Ideal.Quotient.mk_surjective (τ₁ (Ideal.Quotient.mk Q x))
    apply hf
    dsimp [f] at h₁ h₂ ⊢
    refine .trans ?_ (σ.symm_apply_apply _)
    rw [← h₁, ← e, h₂]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, e⟩ := Ideal.Quotient.mk_surjective (τ₂ (Ideal.Quotient.mk Q x))
    apply hf
    dsimp [f] at h₁ h₂ ⊢
    refine .trans ?_ (σ.apply_symm_apply _)
    rw [← h₂, ← e, h₁]

end normal

namespace IsFractionRing

variable (G A B K L : Type*) [Group G] [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
  [Algebra K L] [Algebra A K] [Algebra B L] [Algebra A L] [IsFractionRing A K] [IsFractionRing B L]
  [IsScalarTower A K L] [IsScalarTower A B L] [MulSemiringAction G B] [MulSemiringAction G L]
  [SMulDistribClass G B L] [hAB : Algebra.IsInvariant A B G] [SMulCommClass G A B]

/-- If `G` acts on `B/A` with `A` as the fixed subring, then `G` also acts on `L/K` with `K` as
the fixed subfield, where `K` and `L` are the fraction fields of `A` and `B` respectively. -/
/-
**IsFractionRing.isInvariant_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `IsFraction
Ring`。
形式化陈述：isInvariant_of_isIntegral [Algebra.IsIntegral A B] : Algebra.IsInvariant K
 L G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsFractionRing.nontrivial_iff_nontrivial`：nontrivial_iff_nontrivial : No
ntrivial R ↔ Nontrivial S
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `IsAlgebraic.exists_smul_eq_mul`：IsAlgebraic.exists_smul_eq_mul (a : S) {
b : S} (hRb : IsAlgebraic R b) (hb : b in S⁰) : existsᵉ (c : S) (d != (0 : R)), 
d • a = b * c
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Algebra.IsInvariant.isInvariant`：∀ {A : Type u_1} {B : Type u_2} {G : Ty
pe u_3} {inst : CommSemiring A} {inst_1 : Semiring B} {inst_2 : Algebra A B}   {
inst_3 : Group G} {in…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `smul_div₀'`：smul_div₀' (g : α) (x y : β) : g • (x / y) = (g • x) / (g • 
y)
· 使用定理 `smul_algebraMap`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Algebra R A] {α : Type u_2}   [inst_3 : Monoid α] [
inst_…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b

--- 原说明 ---
If `G` acts on `B/A` with `A` as the fixed subring, then `G` also acts on `L/K` 
with `K` as
the fixed subfield, where `K` and `L` are the fraction fields of `A` and `B` res
pectively.
-/
theorem isInvariant_of_isIntegral [Algebra.IsIntegral A B] : Algebra.IsInvariant K L G := by
  refine ⟨fun x h ↦ ?_⟩
  have hc (a : A) : (algebraMap K L) (algebraMap A K a) = (algebraMap B L) (algebraMap A B a) := by
    simp_rw [← IsScalarTower.algebraMap_apply]
  have : Nontrivial A := (IsFractionRing.nontrivial_iff_nontrivial A K).mpr inferInstance
  have : Nontrivial B := (IsFractionRing.nontrivial_iff_nontrivial B L).mpr inferInstance
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective B x
  have hy' : algebraMap B L y ≠ 0 := by simpa using nonZeroDivisors.ne_zero hy
  obtain ⟨b, a, ha, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) y).exists_smul_eq_mul x hy
  rw [mul_comm, Algebra.smul_def, mul_comm] at hb
  replace ha : (algebraMap B L) (algebraMap A B a) ≠ 0 := by simpa [← hc]
  have hxy : algebraMap B L x / algebraMap B L y =
    algebraMap B L b / algebraMap B L (algebraMap A B a) := by
    rw [div_eq_div_iff hy' ha, ← map_mul, hb, map_mul]
  obtain ⟨b, rfl⟩ := hAB.isInvariant b
    (by simpa [ha, hxy, smul_div₀', ← algebraMap.coe_smul'] using h)
  use algebraMap A K b / algebraMap A K a
  rw [hxy, map_div₀, hc, hc]

include A B in
/-- If `G` acts on `B/A` with `A` as the fixed subring, then `G` also acts on `L/K` with `K` as
the fixed subfield, where `K` and `L` are the fraction fields of `A` and `B` respectively. -/
/-
**IsFractionRing.isInvariant** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：isInvariant [Finite G] : Algebra.IsInvariant K L G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsInvariant.isIntegral`：isIntegral [Finite G] : Algebra.IsIntegr
al A B
· 使用定理 `IsFractionRing.isInvariant_of_isIntegral`：isInvariant_of_isIntegral [Alg
ebra.IsIntegral A B] : Algebra.IsInvariant K L G

--- 原说明 ---
If `G` acts on `B/A` with `A` as the fixed subring, then `G` also acts on `L/K` 
with `K` as
the fixed subfield, where `K` and `L` are the fraction fields of `A` and `B` res
pectively.
-/
theorem isInvariant [Finite G] : Algebra.IsInvariant K L G :=
  have := hAB.isIntegral
  isInvariant_of_isIntegral G A B K L

end IsFractionRing

