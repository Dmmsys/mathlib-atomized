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
Definition of `MixedCharZero` / `MixedCharZero` 的定义

English:
class MixedCharZero
  parameters: (p : Nat)
  axioms and operations (2):
    - [toCharZero : CharZero R]
    - charP_quotient : exists I : Ideal R, I != ⊤ ∧ CharP (R ⧸ I) p

中文:
类 MixedCharZero
  参数: (p : 自然数)
  公理与运算 (2 个):
    - [toCharZero : CharZero R]
    - charP_quotient : 存在 I : Ideal R, I != ⊤ ∧ CharP (R ⧸ I) p
-/
class MixedCharZero (p : Nat) : Prop where
  [toCharZero : CharZero R]
  charP_quotient : exists I : Ideal R, I != ⊤ ∧ CharP (R ⧸ I) p

namespace MixedCharZero

/--
lemma `reduce_to_p_prime` / 引理 `reduce_to_p_prime`

English:
lemma reduce_to_p_prime
  given: {P : Prop}
  proof: by
  constructor
  · intro h q q_prime q_mixedChar
    exact h q (Nat.Prime.pos q_prime) q_mixedChar
  · intro h q q_pos q_mixedChar
    rcases q_mixedChar.charP_quotient with ⟨I, hI_ne_top, _⟩
    -- Krull's Thm: There exists a prime ideal `P` such that `I ≤ P`
    rcases Ideal.exists_le_maximal I 

中文:
引理 reduce_to_p_prime
  条件: {P : 命题}
  证明: by
  constructor
  · intro h q q_prime q_mixedChar
    exact h q (Nat.Prime.pos q_prime) q_mixedChar
  · intro h q q_pos q_mixedChar
    rcases q_mixedChar.charP_quotient with ⟨I, hI_ne_top, _⟩
    -- Krull's Thm: There exists a prime ideal `P` such that `I ≤ P`
    rcases Ideal.exists_le_maximal I 

Depends on / 依赖: Nat.Prime.pos, charP_quotient, hI_ne_top, q_mixedChar, q_mixedChar.charP_quotient, q_pos, q_prime
-/
lemma reduce_to_p_prime {P : Prop} :
    (forall p > 0, MixedCharZero R p -> P) ↔ forall p : Nat, p.Prime -> MixedCharZero R p -> P := by
  constructor
  · intro h q q_prime q_mixedChar
    exact h q (Nat.Prime.pos q_prime) q_mixedChar
  · intro h q q_pos q_mixedChar
    rcases q_mixedChar.charP_quotient with ⟨I, hI_ne_top, _⟩
    -- Krull's Thm: There exists a prime ideal `P` such that `I ≤ P`
    rcases Ideal.exists_le_maximal I hI_ne_top with ⟨M, hM_max, h_IM⟩
    let r := ringChar (R ⧸ M)
    have r_pos : r != 0 := by
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
lemma `reduce_to_maximal_ideal` / 引理 `reduce_to_maximal_ideal`

English:
lemma reduce_to_maximal_ideal
  given: {p : Nat} (hp : Nat.Prime p)
  proof: by
  constructor
  · intro g
    rcases g with ⟨I, ⟨hI_not_top, _⟩⟩
    -- Krull's Thm: There exists a prime ideal `M` such that `I ≤ M`.
    rcases Ideal.exists_le_maximal I hI_not_top with ⟨M, ⟨hM_max, hM_ge⟩⟩
    use M
    constructor
    · exact hM_max
    · cases CharP.exists (R ⧸ M) with
     

中文:
引理 reduce_to_maximal_ideal
  条件: {p : 自然数} (hp : 自然数.Prime p)
  证明: by
  constructor
  · intro g
    rcases g with ⟨I, ⟨hI_not_top, _⟩⟩
    -- Krull's Thm: There exists a prime ideal `M` such that `I ≤ M`.
    rcases Ideal.exists_le_maximal I hI_not_top with ⟨M, ⟨hM_max, hM_ge⟩⟩
    use M
    constructor
    · exact hM_max
    · cases CharP.exists (R ⧸ M) with
     

Depends on / 依赖: hI_not_top
-/
lemma reduce_to_maximal_ideal {p : Nat} (hp : Nat.Prime p) :
    (exists I : Ideal R, I != ⊤ ∧ CharP (R ⧸ I) p) ↔ exists I : Ideal R, I.IsMaximal ∧ CharP (R ⧸ I) p := by
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

/--
lemma `of_algebraRat` / 引理 `of_algebraRat`

English:
lemma of_algebraRat
  given: [Algebra Rat R]
  statement: forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I)
  proof: by
  intro I hI
  constructor
  intro a b h_ab
  contrapose! hI
  -- `↑a - ↑b` is a unit contained in `I`, which contradicts `I ≠ ⊤`.
  refine I.eq_top_of_isUnit_mem ?_ (IsUnit.map (algebraMap Rat R) (IsUnit.mk0 (a - b : Rat) ?_))
  · simpa only [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zer

中文:
引理 of_algebraRat
  条件: [Algebra Rat R]
  结论: 对任意 I : Ideal R, I != ⊤ -> CharZero (R ⧸ I)
  证明: by
  intro I hI
  constructor
  intro a b h_ab
  contrapose! hI
  -- `↑a - ↑b` is a unit contained in `I`, which contradicts `I ≠ ⊤`.
  refine I.eq_top_of_isUnit_mem ?_ (IsUnit.map (algebraMap Rat R) (IsUnit.mk0 (a - b : Rat) ?_))
  · simpa only [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zer
-/
private lemma of_algebraRat [Algebra Rat R] : forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I) := by
  intro I hI
  constructor
  intro a b h_ab
  contrapose! hI
  -- `↑a - ↑b` is a unit contained in `I`, which contradicts `I ≠ ⊤`.
  refine I.eq_top_of_isUnit_mem ?_ (IsUnit.map (algebraMap Rat R) (IsUnit.mk0 (a - b : Rat) ?_))
  · simpa only [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_natCast]
  simpa only [Ne, sub_eq_zero] using (@Nat.cast_injective Rat _ _).ne hI

/-!
The construction of the algebra map `ℚ →+* R` (given by `x ↦ (x.num : R) /ₚ ↑x.pnatDen`)
is marked `private` as it is considered an implementation detail.
-/
section ConstructionAlgebraRat

variable {R}

/--
lemma `PNat.isUnit_natCast` / 引理 `PNat.isUnit_natCast`

English:
lemma PNat.isUnit_natCast
  statement: [h : Fact (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))]
  proof: by
  -- `n : R` is a unit iff `(n)` is not a proper ideal in `R`.
  rw [← Ideal.span_singleton_eq_top]
  -- So by contrapositive, we should show the quotient does not have characteristic zero.
  apply not_imp_comm.mp (h.elim (Ideal.span {↑n}))
  intro h_char_zero
  -- In particular, the image of `n`

中文:
引理 PNat.isUnit_natCast
  结论: [h : Fact (对任意 I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))]
  证明: by
  -- `n : R` is a unit iff `(n)` is not a proper ideal in `R`.
  rw [← Ideal.span_singleton_eq_top]
  -- So by contrapositive, we should show the quotient does not have characteristic zero.
  apply not_imp_comm.mp (h.elim (Ideal.span {↑n}))
  intro h_char_zero
  -- In particular, the image of `n`
-/
private lemma PNat.isUnit_natCast [h : Fact (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))]
    (n : Nat+) : IsUnit (n : R) := by
  -- `n : R` is a unit iff `(n)` is not a proper ideal in `R`.
  rw [← Ideal.span_singleton_eq_top]
  -- So by contrapositive, we should show the quotient does not have characteristic zero.
  apply not_imp_comm.mp (h.elim (Ideal.span {↑n}))
  intro h_char_zero
  -- In particular, the image of `n` in the quotient should be nonzero.
  apply h_char_zero.cast_injective.ne n.ne_zero
  -- But `n` generates the ideal, so its image is clearly zero.
  rw [← map_natCast (Ideal.Quotient.mk _)]; rw [Nat.cast_zero]; rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

@[coe]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def pnatCast [Fact (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))]
  body: fun n => (PNat.isUnit_natCast n).unit

中文:
定义 noncomputable
  签名: def pnatCast [Fact (对任意 I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))]
  定义体: fun n => (PNat.isUnit_natCast n).unit
-/
private noncomputable def pnatCast [Fact (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))] : Nat+ -> Rˣ :=
  fun n => (PNat.isUnit_natCast n).unit

/--
Instance `noncomputable` / 实例 `noncomputable`

English:
instance noncomputable
  signature: instance coePNatUnits
  body: ⟨EqualCharZero.pnatCast⟩

@[simp]

中文:
实例 noncomputable
  签名: instance coeP自然数Units
  定义体: ⟨EqualCharZero.pnatCast⟩

@[simp]
-/
private noncomputable instance coePNatUnits
    [Fact (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))] : Coe Nat+ Rˣ :=
  ⟨EqualCharZero.pnatCast⟩

@[simp]
/--
lemma `pnatCast_one` / 引理 `pnatCast_one`

English:
lemma pnatCast_one
  given: [Fact (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))]
  proof: by
  apply Units.ext
  rw [Units.val_one]
  change ((PNat.isUnit_natCast (R := R) 1).unit : R) = 1
  rw [IsUnit.unit_spec (PNat.isUnit_natCast 1)]
  rw [PNat.one_coe]; rw [Nat.cast_one]

@[simp]

中文:
引理 pnatCast_one
  条件: [Fact (对任意 I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))]
  证明: by
  apply Units.ext
  rw [Units.val_one]
  change ((PNat.isUnit_natCast (R := R) 1).unit : R) = 1
  rw [IsUnit.unit_spec (PNat.isUnit_natCast 1)]
  rw [PNat.one_coe]; rw [Nat.cast_one]

@[simp]
-/
private lemma pnatCast_one [Fact (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))] :
    ((1 : Nat+) : Rˣ) = 1 := by
  apply Units.ext
  rw [Units.val_one]
  change ((PNat.isUnit_natCast (R := R) 1).unit : R) = 1
  rw [IsUnit.unit_spec (PNat.isUnit_natCast 1)]
  rw [PNat.one_coe]; rw [Nat.cast_one]

@[simp]
/--
lemma `pnatCast_eq_natCast` / 引理 `pnatCast_eq_natCast`

English:
lemma pnatCast_eq_natCast
  given: [Fact (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))] (n : Nat+)
  proof: by
  change ((PNat.isUnit_natCast (R := R) n).unit : R) = ↑n
  simp only [IsUnit.unit_spec]

中文:
引理 pnatCast_eq_natCast
  条件: [Fact (对任意 I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))] (n : 自然数+)
  证明: by
  change ((PNat.isUnit_natCast (R := R) n).unit : R) = ↑n
  simp only [IsUnit.unit_spec]
-/
private lemma pnatCast_eq_natCast [Fact (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))] (n : Nat+) :
    ((n : Rˣ) : R) = ↑n := by
  change ((PNat.isUnit_natCast (R := R) n).unit : R) = ↑n
  simp only [IsUnit.unit_spec]

/-- Equal characteristic implies `ℚ`-algebra. -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def algebraRat (h : forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))
  body: haveI : Fact (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I)) := ⟨h⟩
  RingHom.toAlgebra
  { toFun := fun x => x.num /ₚ ↑x.pnatDen
    map_zero' := by simp [divp]
    map_one' := by simp
    map_mul' := by
      intro a b
      simp only [← divp_assoc, divp_mul_eq_mul_divp, divp_divp_eq_divp_mul, di

中文:
定义 noncomputable
  签名: def algebraRat (h : 对任意 I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))
  定义体: haveI : Fact (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I)) := ⟨h⟩
  RingHom.toAlgebra
  { toFun := fun x => x.num /ₚ ↑x.pnatDen
    map_zero' := by simp [divp]
    map_one' := by simp
    map_mul' := by
      intro a b
      simp only [← divp_assoc, divp_mul_eq_mul_divp, divp_divp_eq_divp_mul, di
-/
private noncomputable def algebraRat (h : forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I)) :
    Algebra Rat R :=
  haveI : Fact (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I)) := ⟨h⟩
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

/--
lemma `of_not_mixedCharZero` / 引理 `of_not_mixedCharZero`

English:
lemma of_not_mixedCharZero
  given: [CharZero R] (h : forall p > 0, ¬MixedCharZero R p)
  proof: by
  intro I hI_ne_top
  suffices CharP (R ⧸ I) 0 from CharP.charP_to_charZero _
  cases CharP.exists (R ⧸ I) with
  | intro p hp =>
    cases p with
    | zero => exact hp
    | succ p =>
      have h_mixed : MixedCharZero R p.succ := ⟨⟨I, ⟨hI_ne_top, hp⟩⟩⟩
      exact absurd h_mixed (h p.succ p.su

中文:
引理 of_not_mixedCharZero
  条件: [CharZero R] (h : 对任意 p > 0, ¬MixedCharZero R p)
  证明: by
  intro I hI_ne_top
  suffices CharP (R ⧸ I) 0 from CharP.charP_to_charZero _
  cases CharP.exists (R ⧸ I) with
  | intro p hp =>
    cases p with
    | zero => exact hp
    | succ p =>
      have h_mixed : MixedCharZero R p.succ := ⟨⟨I, ⟨hI_ne_top, hp⟩⟩⟩
      exact absurd h_mixed (h p.succ p.su
-/
private lemma of_not_mixedCharZero [CharZero R] (h : forall p > 0, ¬MixedCharZero R p) :
    forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I) := by
  intro I hI_ne_top
  suffices CharP (R ⧸ I) 0 from CharP.charP_to_charZero _
  cases CharP.exists (R ⧸ I) with
  | intro p hp =>
    cases p with
    | zero => exact hp
    | succ p =>
      have h_mixed : MixedCharZero R p.succ := ⟨⟨I, ⟨hI_ne_top, hp⟩⟩⟩
      exact absurd h_mixed (h p.succ p.succ_pos)

/--
lemma `to_not_mixedCharZero` / 引理 `to_not_mixedCharZero`

English:
lemma to_not_mixedCharZero
  given: (h : forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))
  proof: by
  intro p p_pos
  by_contra hp_mixedChar
  rcases hp_mixedChar.charP_quotient with ⟨I, hI_ne_top, hI_p⟩
  replace hI_zero : CharP (R ⧸ I) 0 := @CharP.ofCharZero _ _ (h I hI_ne_top)
  exact absurd (CharP.eq (R ⧸ I) hI_p hI_zero) (ne_of_gt p_pos)

中文:
引理 to_not_mixedCharZero
  条件: (h : 对任意 I : Ideal R, I != ⊤ -> CharZero (R ⧸ I))
  证明: by
  intro p p_pos
  by_contra hp_mixedChar
  rcases hp_mixedChar.charP_quotient with ⟨I, hI_ne_top, hI_p⟩
  replace hI_zero : CharP (R ⧸ I) 0 := @CharP.ofCharZero _ _ (h I hI_ne_top)
  exact absurd (CharP.eq (R ⧸ I) hI_p hI_zero) (ne_of_gt p_pos)
-/
private lemma to_not_mixedCharZero (h : forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I)) :
    forall p > 0, ¬MixedCharZero R p := by
  intro p p_pos
  by_contra hp_mixedChar
  rcases hp_mixedChar.charP_quotient with ⟨I, hI_ne_top, hI_p⟩
  replace hI_zero : CharP (R ⧸ I) 0 := @CharP.ofCharZero _ _ (h I hI_ne_top)
  exact absurd (CharP.eq (R ⧸ I) hI_p hI_zero) (ne_of_gt p_pos)

/--
theorem `iff_not_mixedCharZero` / 定理 `iff_not_mixedCharZero`

English:
theorem iff_not_mixedCharZero
  given: [CharZero R]
  proof: ⟨to_not_mixedCharZero R, of_not_mixedCharZero R⟩

中文:
定理 iff_not_mixedCharZero
  条件: [CharZero R]
  证明: ⟨to_not_mixedCharZero R, of_not_mixedCharZero R⟩

Depends on / 依赖: of_not_mixedCharZero, to_not_mixedCharZero
-/
theorem iff_not_mixedCharZero [CharZero R] :
    (forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I)) ↔ forall p > 0, ¬MixedCharZero R p :=
  ⟨to_not_mixedCharZero R, of_not_mixedCharZero R⟩

/--
theorem `nonempty_algebraRat_iff` / 定理 `nonempty_algebraRat_iff`

English:
theorem nonempty_algebraRat_iff
  proof: by
  constructor
  · intro h_alg
    have h_alg' : Algebra Rat R := h_alg.some
    apply of_algebraRat
  · intro h
    apply Nonempty.intro
    exact algebraRat h

中文:
定理 nonempty_algebraRat_iff
  证明: by
  constructor
  · intro h_alg
    have h_alg' : Algebra Rat R := h_alg.some
    apply of_algebraRat
  · intro h
    apply Nonempty.intro
    exact algebraRat h

Depends on / 依赖: Algebra, Nonempty, Nonempty.intro, algebraRat, h_alg, h_alg.some, of_algebraRat
-/
theorem nonempty_algebraRat_iff :
    Nonempty (Algebra Rat R) ↔ forall I : Ideal R, I != ⊤ -> CharZero (R ⧸ I) := by
  constructor
  · intro h_alg
    have h_alg' : Algebra Rat R := h_alg.some
    apply of_algebraRat
  · intro h
    apply Nonempty.intro
    exact algebraRat h

end EqualCharZero

/--
lemma `isEmpty_algebraRat_iff_mixedCharZero` / 引理 `isEmpty_algebraRat_iff_mixedCharZero`

English:
lemma isEmpty_algebraRat_iff_mixedCharZero
  given: [CharZero R]
  proof: by
  contrapose!
  rw [← EqualCharZero.iff_not_mixedCharZero]
  apply EqualCharZero.nonempty_algebraRat_iff

中文:
引理 isEmpty_algebraRat_iff_mixedCharZero
  条件: [CharZero R]
  证明: by
  contrapose!
  rw [← EqualCharZero.iff_not_mixedCharZero]
  apply EqualCharZero.nonempty_algebraRat_iff

Depends on / 依赖: EqualCharZero, EqualCharZero.iff_not_mixedCharZero, EqualCharZero.nonempty_algebraRat_iff, contrapose, iff_not_mixedCharZero, nonempty_algebraRat_iff
-/
lemma isEmpty_algebraRat_iff_mixedCharZero [CharZero R] :
    IsEmpty (Algebra Rat R) ↔ exists p > 0, MixedCharZero R p := by
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

/--
theorem `split_equalCharZero_mixedCharZero` / 定理 `split_equalCharZero_mixedCharZero`

English:
theorem split_equalCharZero_mixedCharZero
  statement: [CharZero R] (h_equal : Algebra Rat R -> P)
  proof: by
  by_cases h : exists p > 0, MixedCharZero R p
  · rcases h with ⟨p, ⟨H, hp⟩⟩
    rw [← MixedCharZero.reduce_to_p_prime] at h_mixed
    exact h_mixed p H hp
  · apply h_equal
    rw [← isEmpty_algebraRat_iff_mixedCharZero]; rw [not_isEmpty_iff] at h
    exact h.some

中文:
定理 split_equalCharZero_mixedCharZero
  结论: [CharZero R] (h_equal : Algebra Rat R -> P)
  证明: by
  by_cases h : exists p > 0, MixedCharZero R p
  · rcases h with ⟨p, ⟨H, hp⟩⟩
    rw [← MixedCharZero.reduce_to_p_prime] at h_mixed
    exact h_mixed p H hp
  · apply h_equal
    rw [← isEmpty_algebraRat_iff_mixedCharZero]; rw [not_isEmpty_iff] at h
    exact h.some

Depends on / 依赖: MixedCharZero, MixedCharZero.reduce_to_p_prime, h.some, h_equal, h_mixed, isEmpty_algebraRat_iff_mixedCharZero, not_isEmpty_iff, reduce_to_p_prime
-/
theorem split_equalCharZero_mixedCharZero [CharZero R] (h_equal : Algebra Rat R -> P)
    (h_mixed : forall p : Nat, Nat.Prime p -> MixedCharZero R p -> P) : P := by
  by_cases h : exists p > 0, MixedCharZero R p
  · rcases h with ⟨p, ⟨H, hp⟩⟩
    rw [← MixedCharZero.reduce_to_p_prime] at h_mixed
    exact h_mixed p H hp
  · apply h_equal
    rw [← isEmpty_algebraRat_iff_mixedCharZero]; rw [not_isEmpty_iff] at h
    exact h.some

/--
theorem `split_by_characteristic` / 定理 `split_by_characteristic`

English:
theorem split_by_characteristic
  statement: (h_pos : forall p : Nat, p != 0 -> CharP R p -> P)
  proof: by
  cases CharP.exists R with
  | intro p p_charP =>
    by_cases h : p = 0
    · rw [h] at p_charP
      have h0 : CharZero R := CharP.charP_to_charZero R
      exact split_equalCharZero_mixedCharZero R h_equal h_mixed
    · exact h_pos p h p_charP

中文:
定理 split_by_characteristic
  结论: (h_pos : 对任意 p : 自然数, p != 0 -> CharP R p -> P)
  证明: by
  cases CharP.exists R with
  | intro p p_charP =>
    by_cases h : p = 0
    · rw [h] at p_charP
      have h0 : CharZero R := CharP.charP_to_charZero R
      exact split_equalCharZero_mixedCharZero R h_equal h_mixed
    · exact h_pos p h p_charP

Depends on / 依赖: CharP.charP_to_charZero, CharP.exists, CharZero, charP_to_charZero, h_equal, h_mixed, h_pos, p_charP, split_equalCharZero_mixedCharZero
-/
theorem split_by_characteristic (h_pos : forall p : Nat, p != 0 -> CharP R p -> P)
    (h_equal : Algebra Rat R -> P)
    (h_mixed : forall p : Nat, Nat.Prime p -> MixedCharZero R p -> P) : P := by
  cases CharP.exists R with
  | intro p p_charP =>
    by_cases h : p = 0
    · rw [h] at p_charP
      have h0 : CharZero R := CharP.charP_to_charZero R
      exact split_equalCharZero_mixedCharZero R h_equal h_mixed
    · exact h_pos p h p_charP

/--
theorem `split_by_characteristic_domain` / 定理 `split_by_characteristic_domain`

English:
theorem split_by_characteristic_domain
  statement: [IsDomain R]
  proof: by
  refine split_by_characteristic R ?_ h_equal h_mixed
  intro p p_pos p_char
  have p_prime : Nat.Prime p := or_iff_not_imp_right.mp (CharP.char_is_prime_or_zero R p) p_pos
  exact h_pos p p_prime p_char

中文:
定理 split_by_characteristic_domain
  结论: [IsDomain R]
  证明: by
  refine split_by_characteristic R ?_ h_equal h_mixed
  intro p p_pos p_char
  have p_prime : Nat.Prime p := or_iff_not_imp_right.mp (CharP.char_is_prime_or_zero R p) p_pos
  exact h_pos p p_prime p_char

Depends on / 依赖: CharP.char_is_prime_or_zero, Nat.Prime, char_is_prime_or_zero, h_equal, h_mixed, h_pos, or_iff_not_imp_right, or_iff_not_imp_right.mp, p_char, p_pos, p_prime, split_by_characteristic
-/
theorem split_by_characteristic_domain [IsDomain R]
    (h_pos : forall p : Nat, Nat.Prime p -> CharP R p -> P)
    (h_equal : Algebra Rat R -> P) (h_mixed : forall p : Nat, Nat.Prime p -> MixedCharZero R p -> P) : P := by
  refine split_by_characteristic R ?_ h_equal h_mixed
  intro p p_pos p_char
  have p_prime : Nat.Prime p := or_iff_not_imp_right.mp (CharP.char_is_prime_or_zero R p) p_pos
  exact h_pos p p_prime p_char

/--
theorem `split_by_characteristic_localRing` / 定理 `split_by_characteristic_localRing`

English:
theorem split_by_characteristic_localRing
  statement: [IsLocalRing R]
  proof: by
  refine split_by_characteristic R ?_ h_equal h_mixed
  intro p p_pos p_char
  have p_ppow : IsPrimePow (p : Nat) := or_iff_not_imp_left.mp (charP_zero_or_prime_power R p) p_pos
  exact h_pos p p_ppow p_char

中文:
定理 split_by_characteristic_localRing
  结论: [IsLocalRing R]
  证明: by
  refine split_by_characteristic R ?_ h_equal h_mixed
  intro p p_pos p_char
  have p_ppow : IsPrimePow (p : Nat) := or_iff_not_imp_left.mp (charP_zero_or_prime_power R p) p_pos
  exact h_pos p p_ppow p_char

Depends on / 依赖: IsPrimePow, charP_zero_or_prime_power, h_equal, h_mixed, h_pos, or_iff_not_imp_left, or_iff_not_imp_left.mp, p_char, p_pos, p_ppow, split_by_characteristic
-/
theorem split_by_characteristic_localRing [IsLocalRing R]
    (h_pos : forall p : Nat, IsPrimePow p -> CharP R p -> P) (h_equal : Algebra Rat R -> P)
    (h_mixed : forall p : Nat, Nat.Prime p -> MixedCharZero R p -> P) : P := by
  refine split_by_characteristic R ?_ h_equal h_mixed
  intro p p_pos p_char
  have p_ppow : IsPrimePow (p : Nat) := or_iff_not_imp_left.mp (charP_zero_or_prime_power R p) p_pos
  exact h_pos p p_ppow p_char

end MainStatements
