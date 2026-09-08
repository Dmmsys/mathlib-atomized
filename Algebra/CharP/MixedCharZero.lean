/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.CharP.LocalRing

/-!
# Equal and mixed characteristic

In commutative algebra, some statements are simpler when working over a `ℚ`-algebra `R`, in which
case one also says that the ring has "equal characteristic zero". A ring that is not a
`ℚ`-algebra has either positive characteristic or there exists a prime ideal `I ⊂ R` such that
the quotient `R ⧸ I` has positive characteristic `p > 0`. In this case one speaks of
"mixed characteristic `(0, p)`", where `p` is only unique if `R` is local.

Examples of mixed characteristic rings are `ℤ` or the `p`-adic integers/numbers.

This file provides the main theorem `split_by_characteristic` that splits any proposition `P` into
the following three cases:

1) Positive characteristic: `CharP R p` (where `p ≠ 0`)
2) Equal characteristic zero: `Algebra ℚ R`
3) Mixed characteristic: `MixedCharZero R p` (where `p` is prime)

## Main definitions

- `MixedCharZero` : A ring has mixed characteristic `(0, p)` if it has characteristic zero
  and there exists an ideal such that the quotient `R ⧸ I` has characteristic `p`.

## Main results

- `split_equalCharZero_mixedCharZero` : Split a statement into equal/mixed characteristic zero.

This main theorem has the following three corollaries which include the positive
characteristic case for convenience:

- `split_by_characteristic` : Generally consider positive char `p ≠ 0`.
- `split_by_characteristic_domain` : In a domain we can assume that `p` is prime.
- `split_by_characteristic_localRing` : In a local ring we can assume that `p` is a prime power.

## Implementation Notes

We use the terms `EqualCharZero` and `AlgebraRat` despite there not being any such definitions
in mathlib.
The former refers to the statement `∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)`, the latter
refers to the existence of an instance `[Algebra ℚ R]`. The two are shown to be
equivalent conditions.

## TODO

- Relate mixed characteristic in a local ring to p-adic numbers [NumberTheory.PAdics].
-/

public section

variable (R : Type*) [CommRing R]

/-!
### Mixed characteristic
-/

/--
A ring of characteristic zero is of "mixed characteristic `(0, p)`" if there exists an ideal
such that the quotient `R ⧸ I` has characteristic `p`.

**Remark:** For `p = 0`, `MixedChar R 0` is a meaningless definition (i.e. satisfied by any ring)
as `R ⧸ ⊥ ≅ R` has by definition always characteristic zero.
One could require `(I ≠ ⊥)` in the definition, but then `MixedChar R 0` would mean something
like `ℤ`-algebra of extension degree `≥ 1` and would be completely independent from
whether something is a `ℚ`-algebra or not (e.g. `ℚ[X]` would satisfy it but `ℚ` wouldn't).
-/
/-
**MixedCharZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [CommRing R] → ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring of characteristic zero is of "mixed characteristic `(0, p)`" if there exi
sts an ideal
such that the quotient `R ⧸ I` has characteristic `p`.

**Remark:** For `p = 0`, `MixedChar R 0` is a meaningless definition (i.e. satis
fied by any ring)
as `R ⧸ ⊥ ≅ R` has by definition always characteristic zero.
One could require `(I ≠ ⊥)` in the definition, but then `MixedChar R 0` would me
an something
like `ℤ`-algebra of extension degree `≥ 1` and would be completely independent f
rom
whether something is a `ℚ`-algebra or not (e.g. `ℚ[X]` would satisfy it but `ℚ` 
wouldn't).
-/
class MixedCharZero (p : ℕ) : Prop where
  [toCharZero : CharZero R]
  charP_quotient : ∃ I : Ideal R, I ≠ ⊤ ∧ CharP (R ⧸ I) p

namespace MixedCharZero

/--
Reduction to `p` prime: When proving any statement `P` about mixed characteristic rings we
can always assume that `p` is prime.
-/
/-
**MixedCharZero.reduce_to_p_prime** 是 Mathlib 中的一个引理，位于命名空间 `MixedCharZero`。
形式化陈述：reduce_to_p_prime {P : Prop} : (forall p > 0, MixedCharZero R p -> P) ↔ fo
rall p : Nat, p.Prime -> MixedCharZero R p -> P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `MixedCharZero.charP_quotient`：∀ {R : Type u_1} {inst : CommRing R} {p : 
ℕ} [self : MixedCharZero R p], ∃ I, I ≠ ⊤ ∧ CharP (R ⧸ I) p
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `MixedCharZero.toCharZero`：∀ {R : Type u_1} {inst : CommRing R} (p : ℕ) [
self : MixedCharZero R p], CharZero R
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用引理 `ringChar.of_eq`：of_eq {p : Nat} (h : ringChar R = p) : CharP R p

--- 原说明 ---
Reduction to `p` prime: When proving any statement `P` about mixed characteristi
c rings we
can always assume that `p` is prime.
-/
lemma reduce_to_p_prime {P : Prop} :
    (∀ p > 0, MixedCharZero R p → P) ↔ ∀ p : ℕ, p.Prime → MixedCharZero R p → P := by
  constructor
  · intro h q q_prime q_mixedChar
    exact h q (Nat.Prime.pos q_prime) q_mixedChar
  · intro h q q_pos q_mixedChar
    rcases q_mixedChar.charP_quotient with ⟨I, hI_ne_top, _⟩
    -- Krull's Thm: There exists a prime ideal `P` such that `I ≤ P`
    rcases Ideal.exists_le_maximal I hI_ne_top with ⟨M, hM_max, h_IM⟩
    let r := ringChar (R ⧸ M)
    have r_pos : r ≠ 0 := by
      have q_zero :=
        congr_arg (Ideal.Quotient.factor h_IM) (CharP.cast_eq_zero (R ⧸ I) q)
      simp only [map_natCast, map_zero] at q_zero
      apply ne_zero_of_dvd_ne_zero (ne_of_gt q_pos)
      exact (CharP.cast_eq_zero_iff (R ⧸ M) r q).mp q_zero
    have r_prime : Nat.Prime r :=
      or_iff_not_imp_right.1 (CharP.char_is_prime_or_zero (R ⧸ M) r) r_pos
    apply h r r_prime
    have : CharZero R := q_mixedChar.toCharZero
    exact ⟨⟨M, hM_max.ne_top, ringChar.of_eq rfl⟩⟩

/--
Reduction to `I` prime ideal: When proving statements about mixed characteristic rings,
after we reduced to `p` prime, we can assume that the ideal `I` in the definition is maximal.
-/
/-
**MixedCharZero.reduce_to_maximal_ideal** 是 Mathlib 中的一个引理，位于命名空间 `MixedCharZero
`。
形式化陈述：reduce_to_maximal_ideal {p : Nat} (hp : Nat.Prime p) : (exists I : Ideal R
, I != ⊤ ∧ CharP (R ⧸ I) p) ↔ exists I : Ideal R, I.IsMaximal ∧ CharP (R ⧸ I) p
参数：hp : Nat.Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.Prime.eq_one_or_self_of_dvd`：∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣
 p → m = 1 ∨ m = p
· 使用引理 `CharP.char_ne_one`：char_ne_one [Nontrivial R] (p : Nat) [hc : CharP R p]
 : p != 1
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤

--- 原说明 ---
Reduction to `I` prime ideal: When proving statements about mixed characteristic
 rings,
after we reduced to `p` prime, we can assume that the ideal `I` in the definitio
n is maximal.
-/
lemma reduce_to_maximal_ideal {p : ℕ} (hp : Nat.Prime p) :
    (∃ I : Ideal R, I ≠ ⊤ ∧ CharP (R ⧸ I) p) ↔ ∃ I : Ideal R, I.IsMaximal ∧ CharP (R ⧸ I) p := by
  constructor
  · intro g
    rcases g with ⟨I, ⟨hI_not_top, _⟩⟩
    -- Krull's Thm: There exists a prime ideal `M` such that `I ≤ M`.
    rcases Ideal.exists_le_maximal I hI_not_top with ⟨M, ⟨hM_max, hM_ge⟩⟩
    use M
    constructor
    · exact hM_max
    · cases CharP.exists (R ⧸ M) with
      | intro r hr =>
        convert! hr
        have r_dvd_p : r ∣ p := by
          rw [← CharP.cast_eq_zero_iff (R ⧸ M) r p]
          convert! congr_arg (Ideal.Quotient.factor hM_ge) (CharP.cast_eq_zero (R ⧸ I) p)
        symm
        apply (Nat.Prime.eq_one_or_self_of_dvd hp r r_dvd_p).resolve_left
        exact CharP.char_ne_one (R ⧸ M) r
  · intro ⟨I, hI_max, h_charP⟩
    use I
    exact ⟨Ideal.IsMaximal.ne_top hI_max, h_charP⟩

end MixedCharZero

/-!
### Equal characteristic zero

A commutative ring `R` has "equal characteristic zero" if it satisfies one of the following
equivalent properties:

1) `R` is a `ℚ`-algebra.
2) The quotient `R ⧸ I` has characteristic zero for any proper ideal `I ⊂ R`.
3) `R` has characteristic zero and does not have mixed characteristic for any prime `p`.

We show `(1) ↔ (2) ↔ (3)`, and most of the following is concerned with constructing
an explicit algebra map `ℚ →+* R` (given by `x ↦ (x.num : R) /ₚ ↑x.pnatDen`)
for the direction `(1) ← (2)`.

Note: Property `(2)` is denoted as `EqualCharZero` in the statement names below.
-/

namespace EqualCharZero

/-- `ℚ`-algebra implies equal characteristic. -/
/-
**EqualCharZero.of_algebraRat** 是 Mathlib 中的一个引理，位于命名空间 `EqualCharZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℚ`-algebra implies equal characteristic.
-/
private lemma of_algebraRat [Algebra ℚ R] : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  intro I hI
  constructor
  intro a b h_ab
  contrapose! hI
  -- `↑a - ↑b` is a unit contained in `I`, which contradicts `I ≠ ⊤`.
  refine I.eq_top_of_isUnit_mem ?_ (IsUnit.map (algebraMap ℚ R) (IsUnit.mk0 (a - b : ℚ) ?_))
  · simpa only [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_natCast]
  simpa only [Ne, sub_eq_zero] using (@Nat.cast_injective ℚ _ _).ne hI

/-!
The construction of the algebra map `ℚ →+* R` (given by `x ↦ (x.num : R) /ₚ ↑x.pnatDen`)
is marked `private` as it is considered an implementation detail.
-/
section ConstructionAlgebraRat

variable {R}

/-
**EqualCharZero.PNat.isUnit_natCast** 是 Mathlib 中的一个引理，位于命名空间 `EqualCharZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma PNat.isUnit_natCast [h : Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))]
    (n : ℕ+) : IsUnit (n : R) := by
  -- `n : R` is a unit iff `(n)` is not a proper ideal in `R`.
  rw [← Ideal.span_singleton_eq_top]
  -- So by contrapositive, we should show the quotient does not have characteristic zero.
  apply not_imp_comm.mp (h.elim (Ideal.span {↑n}))
  intro h_char_zero
  -- In particular, the image of `n` in the quotient should be nonzero.
  apply h_char_zero.cast_injective.ne n.ne_zero
  -- But `n` generates the ideal, so its image is clearly zero.
  rw [← map_natCast (Ideal.Quotient.mk _), Nat.cast_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

@[coe]
/-
**EqualCharZero.pnatCast** 是 Mathlib 中的一个定义，位于命名空间 `EqualCharZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def pnatCast [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : ℕ+ → Rˣ :=
  fun n => (PNat.isUnit_natCast n).unit
/-
**EqualCharZero.coePNatUnits** 是 Mathlib 中的一个实例，位于命名空间 `EqualCharZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable instance coePNatUnits
    [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : Coe ℕ+ Rˣ :=
  ⟨EqualCharZero.pnatCast⟩

@[simp]
/-
**EqualCharZero.pnatCast_one** 是 Mathlib 中的一个引理，位于命名空间 `EqualCharZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma pnatCast_one [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] :
    ((1 : ℕ+) : Rˣ) = 1 := by
  apply Units.ext
  rw [Units.val_one]
  change ((PNat.isUnit_natCast (R := R) 1).unit : R) = 1
  rw [IsUnit.unit_spec (PNat.isUnit_natCast 1)]
  rw [PNat.one_coe, Nat.cast_one]

@[simp]
/-
**EqualCharZero.pnatCast_eq_natCast** 是 Mathlib 中的一个引理，位于命名空间 `EqualCharZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma pnatCast_eq_natCast [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] (n : ℕ+) :
    ((n : Rˣ) : R) = ↑n := by
  change ((PNat.isUnit_natCast (R := R) n).unit : R) = ↑n
  simp only [IsUnit.unit_spec]

/-- Equal characteristic implies `ℚ`-algebra. -/
@[instance_reducible]
/-
**EqualCharZero.algebraRat** 是 Mathlib 中的一个定义，位于命名空间 `EqualCharZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equal characteristic implies `ℚ`-algebra.
-/
private noncomputable def algebraRat (h : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) :
    Algebra ℚ R :=
  haveI : Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) := ⟨h⟩
  RingHom.toAlgebra
  { toFun := fun x => x.num /ₚ ↑x.pnatDen
    map_zero' := by simp [divp]
    map_one' := by simp
    map_mul' := by
      intro a b
      simp only [← divp_assoc, divp_mul_eq_mul_divp, divp_divp_eq_divp_mul, divp_eq_iff_mul_eq,
        pnatCast_eq_natCast, Rat.coe_pnatDen, Units.val_mul]
      trans (↑((a * b).num * a.den * b.den) : R)
      · simp_rw [Int.cast_mul, Int.cast_natCast]
        ring
      rw [Rat.mul_num_den' a b]
      simp
    map_add' := by
      intro a b
      simp only [Units.add_divp, pnatCast_eq_natCast, Rat.coe_pnatDen, divp_mul_eq_mul_divp,
        Units.divp_add, divp_divp_eq_divp_mul, divp_eq_iff_mul_eq, Units.val_mul]
      trans (↑((a + b).num * a.den * b.den) : R)
      · simp_rw [Int.cast_mul, Int.cast_natCast]
        ring
      rw [Rat.add_num_den' a b]
      simp }

end ConstructionAlgebraRat

/-- Not mixed characteristic implies equal characteristic. -/
/-
**EqualCharZero.of_not_mixedCharZero** 是 Mathlib 中的一个引理，位于命名空间 `EqualCharZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Not mixed characteristic implies equal characteristic.
-/
private lemma of_not_mixedCharZero [CharZero R] (h : ∀ p > 0, ¬MixedCharZero R p) :
    ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  intro I hI_ne_top
  suffices CharP (R ⧸ I) 0 from CharP.charP_to_charZero _
  cases CharP.exists (R ⧸ I) with
  | intro p hp =>
    cases p with
    | zero => exact hp
    | succ p =>
      have h_mixed : MixedCharZero R p.succ := ⟨⟨I, ⟨hI_ne_top, hp⟩⟩⟩
      exact absurd h_mixed (h p.succ p.succ_pos)

/-- Equal characteristic implies not mixed characteristic. -/
/-
**EqualCharZero.to_not_mixedCharZero** 是 Mathlib 中的一个引理，位于命名空间 `EqualCharZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equal characteristic implies not mixed characteristic.
-/
private lemma to_not_mixedCharZero (h : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) :
    ∀ p > 0, ¬MixedCharZero R p := by
  intro p p_pos
  by_contra hp_mixedChar
  rcases hp_mixedChar.charP_quotient with ⟨I, hI_ne_top, hI_p⟩
  replace hI_zero : CharP (R ⧸ I) 0 := @CharP.ofCharZero _ _ (h I hI_ne_top)
  exact absurd (CharP.eq (R ⧸ I) hI_p hI_zero) (ne_of_gt p_pos)

/--
A ring of characteristic zero has equal characteristic iff it does not
have mixed characteristic for any `p`.
-/
/-
**EqualCharZero.iff_not_mixedCharZero** 是 Mathlib 中的一个定理，位于命名空间 `EqualCharZero`。
形式化陈述：iff_not_mixedCharZero [CharZero R] : (forall I : Ideal R, I != ⊤ -> CharZe
ro (R ⧸ I)) ↔ forall p > 0, ¬MixedCharZero R p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.CharP.MixedCharZero.0.EqualCharZero.to_not_mixe
dCharZero`：∀ (R : Type u_1) [inst : CommRing R], (∀ (I : Ideal R), I ≠ ⊤ → CharZ
ero (R ⧸ I)) → ∀ p > 0, ¬MixedCharZero R p
· 使用定理 `_private.Mathlib.Algebra.CharP.MixedCharZero.0.EqualCharZero.of_not_mixe
dCharZero`：∀ (R : Type u_1) [inst : CommRing R] [CharZero R],   (∀ p > 0, ¬Mixed
CharZero R p) → ∀ (I : Ideal R), I ≠ ⊤ → CharZero (R ⧸ I)

--- 原说明 ---
A ring of characteristic zero has equal characteristic iff it does not
have mixed characteristic for any `p`.
-/
theorem iff_not_mixedCharZero [CharZero R] :
    (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) ↔ ∀ p > 0, ¬MixedCharZero R p :=
  ⟨to_not_mixedCharZero R, of_not_mixedCharZero R⟩

/-- A ring is a `ℚ`-algebra iff it has equal characteristic zero. -/
/-
**EqualCharZero.nonempty_algebraRat_iff** 是 Mathlib 中的一个定理，位于命名空间 `EqualCharZero
`。
形式化陈述：nonempty_algebraRat_iff : Nonempty (Algebra Rat R) ↔ forall I : Ideal R, I
 != ⊤ -> CharZero (R ⧸ I)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.CharP.MixedCharZero.0.EqualCharZero.of_algebraR
at`：∀ (R : Type u_1) [inst : CommRing R] [Algebra ℚ R] (I : Ideal R), I ≠ ⊤ → Ch
arZero (R ⧸ I)

--- 原说明 ---
A ring is a `ℚ`-algebra iff it has equal characteristic zero.
-/
theorem nonempty_algebraRat_iff :
    Nonempty (Algebra ℚ R) ↔ ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  constructor
  · intro h_alg
    have h_alg' : Algebra ℚ R := h_alg.some
    apply of_algebraRat
  · intro h
    apply Nonempty.intro
    exact algebraRat h

end EqualCharZero

/--
A ring of characteristic zero is not a `ℚ`-algebra iff it has mixed characteristic for some `p`.
-/
/-
**isEmpty_algebraRat_iff_mixedCharZero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isEmpty_algebraRat_iff_mixedCharZero [CharZero R] : IsEmpty (Algebra Rat R
) ↔ exists p > 0, MixedCharZero R p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EqualCharZero.iff_not_mixedCharZero`：iff_not_mixedCharZero [CharZero R] 
: (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I)) ↔ forall p > 0, ¬MixedCharZer
o R p
· 使用定理 `EqualCharZero.nonempty_algebraRat_iff`：nonempty_algebraRat_iff : Nonempt
y (Algebra Rat R) ↔ forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I)

--- 原说明 ---
A ring of characteristic zero is not a `ℚ`-algebra iff it has mixed characterist
ic for some `p`.
-/
lemma isEmpty_algebraRat_iff_mixedCharZero [CharZero R] :
    IsEmpty (Algebra ℚ R) ↔ ∃ p > 0, MixedCharZero R p := by
  contrapose!
  rw [← EqualCharZero.iff_not_mixedCharZero]
  apply EqualCharZero.nonempty_algebraRat_iff

/-!
### Splitting statements into different characteristic

Statements to split a proof by characteristic. There are 3 theorems here that are very
similar. They only differ in the assumptions we can make on the positive characteristic
case:
Generally we need to consider all `p ≠ 0`, but if `R` is a local ring, we can assume
that `p` is a prime power. And if `R` is a domain, we can even assume that `p` is prime.
-/

section MainStatements

variable {P : Prop}

/-- Split a `Prop` in characteristic zero into equal and mixed characteristic. -/
/-
**split_equalCharZero_mixedCharZero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：split_equalCharZero_mixedCharZero [CharZero R] (h_equal : Algebra Rat R ->
 P) (h_mixed : forall p : Nat, Nat.Prime p -> MixedCharZero R p -> P) : P
参数：h_equal : Algebra Rat R -> P；h_mixed : forall p : Nat, Nat.Prime p -> MixedCh
arZero R p -> P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MixedCharZero.reduce_to_p_prime`：reduce_to_p_prime {P : Prop} : (forall 
p > 0, MixedCharZero R p -> P) ↔ forall p : Nat, p.Prime -> MixedCharZero R p ->
 P
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
· 使用引理 `isEmpty_algebraRat_iff_mixedCharZero`：isEmpty_algebraRat_iff_mixedCharZe
ro [CharZero R] : IsEmpty (Algebra Rat R) ↔ exists p > 0, MixedCharZero R p

--- 原说明 ---
Split a `Prop` in characteristic zero into equal and mixed characteristic.
-/
theorem split_equalCharZero_mixedCharZero [CharZero R] (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  by_cases h : ∃ p > 0, MixedCharZero R p
  · rcases h with ⟨p, ⟨H, hp⟩⟩
    rw [← MixedCharZero.reduce_to_p_prime] at h_mixed
    exact h_mixed p H hp
  · apply h_equal
    rw [← isEmpty_algebraRat_iff_mixedCharZero, not_isEmpty_iff] at h
    exact h.some

/--
Split any `Prop` over `R` into the three cases:
- positive characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
/-
**split_by_characteristic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：split_by_characteristic (h_pos : forall p : Nat, p != 0 -> CharP R p -> P)
 (h_equal : Algebra Rat R -> P) (h_mixed : forall p : Nat, Nat.Prime p -> MixedC
harZero R p -> P) : P
参数：h_pos : forall p : Nat, p != 0 -> CharP R p -> P；h_equal : Algebra Rat R -> P
；h_mixed : forall p : Nat, Nat.Prime p -> MixedCharZero R p -> P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用引理 `CharP.charP_to_charZero`：charP_to_charZero [CharP R 0] : CharZero R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `split_equalCharZero_mixedCharZero`：split_equalCharZero_mixedCharZero [Ch
arZero R] (h_equal : Algebra Rat R -> P) (h_mixed : forall p : Nat, Nat.Prime p 
-> MixedCharZero R p ->…

--- 原说明 ---
Split any `Prop` over `R` into the three cases:
- positive characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
theorem split_by_characteristic (h_pos : ∀ p : ℕ, p ≠ 0 → CharP R p → P)
    (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  cases CharP.exists R with
  | intro p p_charP =>
    by_cases h : p = 0
    · rw [h] at p_charP
      have h0 : CharZero R := CharP.charP_to_charZero R
      exact split_equalCharZero_mixedCharZero R h_equal h_mixed
    · exact h_pos p h p_charP

/--
In an `IsDomain R`, split any `Prop` over `R` into the three cases:
- *prime* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
/-
**split_by_characteristic_domain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：split_by_characteristic_domain [IsDomain R] (h_pos : forall p : Nat, Nat.P
rime p -> CharP R p -> P) (h_equal : Algebra Rat R -> P) (h_mixed : forall p : N
at, Nat.Prime p -> MixedCharZero R p -> P) : P
参数：h_pos : forall p : Nat, Nat.Prime p -> CharP R p -> P；h_equal : Algebra Rat R
 -> P；h_mixed : forall p : Nat, Nat.Prime p -> MixedCharZero R p -> P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `split_by_characteristic`：split_by_characteristic (h_pos : forall p : Nat
, p != 0 -> CharP R p -> P) (h_equal : Algebra Rat R -> P) (h_mixed : forall p :
 Nat, Nat.Pri…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
In an `IsDomain R`, split any `Prop` over `R` into the three cases:
- *prime* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
theorem split_by_characteristic_domain [IsDomain R]
    (h_pos : ∀ p : ℕ, Nat.Prime p → CharP R p → P)
    (h_equal : Algebra ℚ R → P) (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  refine split_by_characteristic R ?_ h_equal h_mixed
  intro p p_pos p_char
  have p_prime : Nat.Prime p := or_iff_not_imp_right.mp (CharP.char_is_prime_or_zero R p) p_pos
  exact h_pos p p_prime p_char

/--
In a local ring `R`, split any predicate over `R` into the three cases:
- *prime power* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
/-
**split_by_characteristic_localRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：split_by_characteristic_localRing [IsLocalRing R] (h_pos : forall p : Nat,
 IsPrimePow p -> CharP R p -> P) (h_equal : Algebra Rat R -> P) (h_mixed : foral
l p : Nat, Nat.Prime p -> MixedCharZero R p -> P) : P
参数：h_pos : forall p : Nat, IsPrimePow p -> CharP R p -> P；h_equal : Algebra Rat 
R -> P；h_mixed : forall p : Nat, Nat.Prime p -> MixedCharZero R p -> P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `split_by_characteristic`：split_by_characteristic (h_pos : forall p : Nat
, p != 0 -> CharP R p -> P) (h_equal : Algebra Rat R -> P) (h_mixed : forall p :
 Nat, Nat.Pri…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `charP_zero_or_prime_power`：charP_zero_or_prime_power (R : Type*) [CommRi
ng R] [IsLocalRing R] (q : Nat) [char_R_q : CharP R q] : q = 0 ∨ IsPrimePow q

--- 原说明 ---
In a local ring `R`, split any predicate over `R` into the three cases:
- *prime power* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
theorem split_by_characteristic_localRing [IsLocalRing R]
    (h_pos : ∀ p : ℕ, IsPrimePow p → CharP R p → P) (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  refine split_by_characteristic R ?_ h_equal h_mixed
  intro p p_pos p_char
  have p_ppow : IsPrimePow (p : ℕ) := or_iff_not_imp_left.mp (charP_zero_or_prime_power R p) p_pos
  exact h_pos p p_ppow p_char

end MainStatements

