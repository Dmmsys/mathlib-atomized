/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.RingTheory.Localization.Defs

/-!
# Integer elements of a localization

## Main definitions

* `IsLocalization.IsInteger` is a predicate stating that `x : S` is in the image of `R`

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section


variable {R : Type*} [CommSemiring R] {M : Submonoid R} {S : Type*} [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

open Function

namespace IsLocalization

section

variable (R)

-- TODO: define a subalgebra of `IsInteger`s
/--
Definition of `IsInteger` / `IsInteger` 的定义

English:
definition IsInteger
  signature: (a : S)
  body: a in (algebraMap R S).rangeS

中文:
定义 Is整数eger
  签名: (a : S)
  定义体: a in (algebraMap R S).rangeS

Depends on / 依赖: algebraMap, rangeS
-/
def IsInteger (a : S) : Prop :=
  a in (algebraMap R S).rangeS

end

/--
theorem `isInteger_zero` / 定理 `isInteger_zero`

English:
theorem isInteger_zero
  statement: IsInteger R (0 : S)
  proof: Subsemiring.zero_mem _

中文:
定理 is整数eger_zero
  结论: Is整数eger R (0 : S)
  证明: Subsemiring.zero_mem _

Depends on / 依赖: Subsemiring, Subsemiring.zero_mem, zero_mem
-/
theorem isInteger_zero : IsInteger R (0 : S) :=
  Subsemiring.zero_mem _

/--
theorem `isInteger_one` / 定理 `isInteger_one`

English:
theorem isInteger_one
  statement: IsInteger R (1 : S)
  proof: Subsemiring.one_mem _

中文:
定理 is整数eger_one
  结论: Is整数eger R (1 : S)
  证明: Subsemiring.one_mem _

Depends on / 依赖: Subsemiring, Subsemiring.one_mem, one_mem
-/
theorem isInteger_one : IsInteger R (1 : S) :=
  Subsemiring.one_mem _

/--
theorem `isInteger_add` / 定理 `isInteger_add`

English:
theorem isInteger_add
  given: {a b : S} (ha : IsInteger R a) (hb : IsInteger R b)
  statement: IsInteger R (a + b)
  proof: Subsemiring.add_mem _ ha hb

中文:
定理 is整数eger_add
  条件: {a b : S} (ha : Is整数eger R a) (hb : Is整数eger R b)
  结论: Is整数eger R (a + b)
  证明: Subsemiring.add_mem _ ha hb

Depends on / 依赖: Subsemiring, Subsemiring.add_mem, add_mem
-/
theorem isInteger_add {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a + b) :=
  Subsemiring.add_mem _ ha hb

/--
theorem `isInteger_mul` / 定理 `isInteger_mul`

English:
theorem isInteger_mul
  given: {a b : S} (ha : IsInteger R a) (hb : IsInteger R b)
  statement: IsInteger R (a * b)
  proof: Subsemiring.mul_mem _ ha hb

中文:
定理 is整数eger_mul
  条件: {a b : S} (ha : Is整数eger R a) (hb : Is整数eger R b)
  结论: Is整数eger R (a * b)
  证明: Subsemiring.mul_mem _ ha hb

Depends on / 依赖: Subsemiring, Subsemiring.mul_mem, mul_mem
-/
theorem isInteger_mul {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a * b) :=
  Subsemiring.mul_mem _ ha hb

/--
theorem `isInteger_smul` / 定理 `isInteger_smul`

English:
theorem isInteger_smul
  given: {a : R} {b : S} (hb : IsInteger R b)
  statement: IsInteger R (a • b)
  proof: by
  rcases hb with ⟨b', hb⟩
  use a * b'
  rw [← hb]; rw [(algebraMap R S).map_mul]; rw [Algebra.smul_def]

中文:
定理 is整数eger_smul
  条件: {a : R} {b : S} (hb : Is整数eger R b)
  结论: Is整数eger R (a • b)
  证明: by
  rcases hb with ⟨b', hb⟩
  use a * b'
  rw [← hb]; rw [(algebraMap R S).map_mul]; rw [Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, algebraMap, map_mul, smul_def
-/
theorem isInteger_smul {a : R} {b : S} (hb : IsInteger R b) : IsInteger R (a • b) := by
  rcases hb with ⟨b', hb⟩
  use a * b'
  rw [← hb]; rw [(algebraMap R S).map_mul]; rw [Algebra.smul_def]

variable (M)
variable [IsLocalization M S]

/--
theorem `exists_integer_multiple'` / 定理 `exists_integer_multiple'`

English:
theorem exists_integer_multiple'
  given: (a : S)
  statement: exists b : M, IsInteger R (a * algebraMap R S b)
  proof: let ⟨⟨Num, denom⟩, h⟩ := IsLocalization.surj _ a
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

中文:
定理 存在_integer_multiple'
  条件: (a : S)
  结论: 存在 b : M, Is整数eger R (a * algebraMap R S b)
  证明: let ⟨⟨Num, denom⟩, h⟩ := IsLocalization.surj _ a
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

Depends on / 依赖: IsLocalization, IsLocalization.surj, Set.mem_range.mpr, h.symm, mem_range
-/
theorem exists_integer_multiple' (a : S) : exists b : M, IsInteger R (a * algebraMap R S b) :=
  let ⟨⟨Num, denom⟩, h⟩ := IsLocalization.surj _ a
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

/--
theorem `exists_integer_multiple` / 定理 `exists_integer_multiple`

English:
theorem exists_integer_multiple
  given: (a : S)
  statement: exists b : M, IsInteger R ((b : R) • a)
  proof: by
  simp_rw [Algebra.smul_def, mul_comm _ a]
  apply exists_integer_multiple'

中文:
定理 存在_integer_multiple
  条件: (a : S)
  结论: 存在 b : M, Is整数eger R ((b : R) • a)
  证明: by
  simp_rw [Algebra.smul_def, mul_comm _ a]
  apply exists_integer_multiple'

Depends on / 依赖: Algebra, Algebra.smul_def, exists_integer_multiple, mul_comm, simp_rw, smul_def
-/
theorem exists_integer_multiple (a : S) : exists b : M, IsInteger R ((b : R) • a) := by
  simp_rw [Algebra.smul_def, mul_comm _ a]
  apply exists_integer_multiple'

/--
theorem `exist_integer_multiples` / 定理 `exist_integer_multiples`

English:
theorem exist_integer_multiples
  given: {ι : Type*} (s : Finset ι) (f : ι -> S)
  proof: by
  have := Classical.propDecidable
  refine ⟨∏ i in s, (sec M (f i)).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j in s.erase i, (sec M (f j)).2) * (sec M (f i)).1
  rw [map_mul]; rw [sec_spec']; rw [← mul_assoc]; rw [← (algebraMap R S).map_mul]; rw [← Algebra.smul_def]
  congr 2
  refine _root_.trans ?_ (map_prod (Submonoid.subtype M) _ _).symm
  rw [mul_comm]; rw [Submonoid.coe_finsetProd]; rw [-- Porting note: explicitly supplied `f`
    ← Finset.prod_insert (f := fun i => ((sec M (f i)).snd : R)) (s.notMem_erase i)]; rw [Finset.insert_erase hi]
  rfl

中文:
定理 exist_integer_multiples
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> S)
  证明: by
  have := Classical.propDecidable
  refine ⟨∏ i in s, (sec M (f i)).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j in s.erase i, (sec M (f j)).2) * (sec M (f i)).1
  rw [map_mul]; rw [sec_spec']; rw [← mul_assoc]; rw [← (algebraMap R S).map_mul]; rw [← Algebra.smul_def]
  congr 2
  refine _root_.trans ?_ (map_prod (Submonoid.subtype M) _ _).symm
  rw [mul_comm]; rw [Submonoid.coe_finsetProd]; rw [-- Porting note: explicitly supplied `f`
    ← Finset.prod_insert (f := fun i => ((sec M (f i)).snd : R)) (s.notMem_erase i)]; rw [Finset.insert_erase hi]
  rfl

Depends on / 依赖: Algebra, Algebra.smul_def, Classical, Classical.propDecidable, Finset, Finset.prod_insert, Porting, Submonoid, Submonoid.coe_finsetProd, Submonoid.subtype, _root_, _root_.trans, algebraMap, coe_finsetProd, explicitly, map_mul, map_prod, mul_assoc, mul_comm, notMem_erase
-/
theorem exist_integer_multiples {ι : Type*} (s : Finset ι) (f : ι -> S) :
    exists b : M, forall i in s, IsLocalization.IsInteger R ((b : R) • f i) := by
  have := Classical.propDecidable
  refine ⟨∏ i in s, (sec M (f i)).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j in s.erase i, (sec M (f j)).2) * (sec M (f i)).1
  rw [map_mul]; rw [sec_spec']; rw [← mul_assoc]; rw [← (algebraMap R S).map_mul]; rw [← Algebra.smul_def]
  congr 2
  refine _root_.trans ?_ (map_prod (Submonoid.subtype M) _ _).symm
  rw [mul_comm]; rw [Submonoid.coe_finsetProd]; rw [-- Porting note: explicitly supplied `f`
    ← Finset.prod_insert (f := fun i => ((sec M (f i)).snd : R)) (s.notMem_erase i)]; rw [Finset.insert_erase hi]
  rfl

/--
theorem `exist_integer_multiples_of_finite` / 定理 `exist_integer_multiples_of_finite`

English:
theorem exist_integer_multiples_of_finite
  given: {ι : Type*} [Finite ι] (f : ι -> S)
  proof: by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples M Finset.univ f
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

中文:
定理 exist_integer_multiples_of_finite
  条件: {ι : 类型} [有限 ι] (f : ι -> S)
  证明: by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples M Finset.univ f
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ, exist_integer_multiples, mem_univ, nonempty_fintype
-/
theorem exist_integer_multiples_of_finite {ι : Type*} [Finite ι] (f : ι -> S) :
    exists b : M, forall i, IsLocalization.IsInteger R ((b : R) • f i) := by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples M Finset.univ f
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

/--
theorem `exist_integer_multiples_of_finset` / 定理 `exist_integer_multiples_of_finset`

English:
theorem exist_integer_multiples_of_finset
  given: (s : Finset S)
  proof: exist_integer_multiples M s id

中文:
定理 exist_integer_multiples_of_finset
  条件: (s : 有限集 S)
  证明: exist_integer_multiples M s id

Depends on / 依赖: exist_integer_multiples
-/
theorem exist_integer_multiples_of_finset (s : Finset S) :
    exists b : M, forall a in s, IsInteger R ((b : R) • a) :=
  exist_integer_multiples M s id

/--
Definition of `commonDenom` / `commonDenom` 的定义

English:
definition commonDenom
  signature: {ι : Type*} (s : Finset ι) (f : ι -> S)
  body: (exist_integer_multiples M s f).choose

中文:
定义 commonDenom
  签名: {ι : 类型} (s : 有限集 ι) (f : ι -> S)
  定义体: (exist_integer_multiples M s f).choose

Depends on / 依赖: exist_integer_multiples
-/
noncomputable def commonDenom {ι : Type*} (s : Finset ι) (f : ι -> S) : M :=
  (exist_integer_multiples M s f).choose

/--
Definition of `integerMultiple` / `integerMultiple` 的定义

English:
definition integerMultiple
  signature: {ι : Type*} (s : Finset ι) (f : ι -> S) (i : s)
  body: ((exist_integer_multiples M s f).choose_spec i i.prop).choose

@[simp]

中文:
定义 integerMultiple
  签名: {ι : 类型} (s : 有限集 ι) (f : ι -> S) (i : s)
  定义体: ((exist_integer_multiples M s f).choose_spec i i.prop).choose

@[simp]

Depends on / 依赖: choose_spec, exist_integer_multiples, i.prop
-/
noncomputable def integerMultiple {ι : Type*} (s : Finset ι) (f : ι -> S) (i : s) : R :=
  ((exist_integer_multiples M s f).choose_spec i i.prop).choose

@[simp]
/--
theorem `map_integerMultiple` / 定理 `map_integerMultiple`

English:
theorem map_integerMultiple
  given: {ι : Type*} (s : Finset ι) (f : ι -> S) (i : s)
  proof: ((exist_integer_multiples M s f).choose_spec _ i.prop).choose_spec

中文:
定理 map_integerMultiple
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> S) (i : s)
  证明: ((exist_integer_multiples M s f).choose_spec _ i.prop).choose_spec

Depends on / 依赖: choose_spec, exist_integer_multiples, i.prop
-/
theorem map_integerMultiple {ι : Type*} (s : Finset ι) (f : ι -> S) (i : s) :
    algebraMap R S (integerMultiple M s f i) = commonDenom M s f • f i :=
  ((exist_integer_multiples M s f).choose_spec _ i.prop).choose_spec

/--
theorem `integerMultiple_injective` / 定理 `integerMultiple_injective`

English:
theorem integerMultiple_injective
  statement: {ι : Type*} (s : Finset ι) (f : ι -> S)
  proof: by
  intro i j h
  rw [← SetLike.coe_eq_coe]; rw [← hf.eq_iff]; rw [← (IsLocalization.smul_bijective S (commonDenom M s f)).injective.eq_iff]; rw [← map_integerMultiple M s f i]; rw [← map_integerMultiple M s f j]; rw [h]

@[deprecated (since := "2026-07-18")] alias integerMultipleMultiple_injective :=
  integerMultiple_injective

中文:
定理 integerMultiple_injective
  结论: {ι : 类型} (s : 有限集 ι) (f : ι -> S)
  证明: by
  intro i j h
  rw [← SetLike.coe_eq_coe]; rw [← hf.eq_iff]; rw [← (IsLocalization.smul_bijective S (commonDenom M s f)).injective.eq_iff]; rw [← map_integerMultiple M s f i]; rw [← map_integerMultiple M s f j]; rw [h]

@[deprecated (since := "2026-07-18")] alias integerMultipleMultiple_injective :=
  integerMultiple_injective

Depends on / 依赖: IsLocalization, IsLocalization.smul_bijective, SetLike, SetLike.coe_eq_coe, coe_eq_coe, commonDenom, eq_iff, hf.eq_iff, injective, injective.eq_iff, map_integerMultiple, smul_bijective
-/
theorem integerMultiple_injective {ι : Type*} (s : Finset ι) (f : ι -> S)
    (hf : Function.Injective f) : Function.Injective (integerMultiple M s f) := by
  intro i j h
  rw [← SetLike.coe_eq_coe]; rw [← hf.eq_iff]; rw [← (IsLocalization.smul_bijective S (commonDenom M s f)).injective.eq_iff]; rw [← map_integerMultiple M s f i]; rw [← map_integerMultiple M s f j]; rw [h]

@[deprecated (since := "2026-07-18")] alias integerMultipleMultiple_injective :=
  integerMultiple_injective

/--
Definition of `commonDenomOfFinset` / `commonDenomOfFinset` 的定义

English:
definition commonDenomOfFinset
  signature: (s : Finset S)
  body: commonDenom M s id

中文:
定义 commonDenomOfFinset
  签名: (s : 有限集 S)
  定义体: commonDenom M s id

Depends on / 依赖: commonDenom
-/
noncomputable def commonDenomOfFinset (s : Finset S) : M :=
  commonDenom M s id

/--
Definition of `finsetIntegerMultiple` / `finsetIntegerMultiple` 的定义

English:
definition finsetIntegerMultiple
  signature: [DecidableEq R] (s : Finset S)
  body: s.attach.image fun t => integerMultiple M s id t

中文:
定义 finset整数egerMultiple
  签名: [DecidableEq R] (s : 有限集 S)
  定义体: s.attach.image fun t => integerMultiple M s id t

Depends on / 依赖: attach, integerMultiple, s.attach.image
-/
noncomputable def finsetIntegerMultiple [DecidableEq R] (s : Finset S) : Finset R :=
  s.attach.image fun t => integerMultiple M s id t

open scoped Pointwise

/--
theorem `finsetIntegerMultiple_image` / 定理 `finsetIntegerMultiple_image`

English:
theorem finsetIntegerMultiple_image
  given: [DecidableEq R] (s : Finset S)
  proof: by
  delta finsetIntegerMultiple commonDenom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [map_integerMultiple]
    exact Set.mem_image_of_mem _ x.prop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integerMultiple M s id _⟩

@[simp]

中文:
定理 finset整数egerMultiple_image
  条件: [DecidableEq R] (s : 有限集 S)
  证明: by
  delta finsetIntegerMultiple commonDenom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [map_integerMultiple]
    exact Set.mem_image_of_mem _ x.prop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integerMultiple M s id _⟩

@[simp]

Depends on / 依赖: Finset, Finset.coe_image, Set.mem_image_of_mem, coe_image, commonDenom, finsetIntegerMultiple, map_integerMultiple, mem_attach, mem_image_of_mem, s.mem_attach, x.prop
-/
theorem finsetIntegerMultiple_image [DecidableEq R] (s : Finset S) :
    algebraMap R S '' finsetIntegerMultiple M s = commonDenomOfFinset M s • (s : Set S) := by
  delta finsetIntegerMultiple commonDenom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [map_integerMultiple]
    exact Set.mem_image_of_mem _ x.prop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integerMultiple M s id _⟩

@[simp]
/--
theorem `card_finsetIntegerMultiple` / 定理 `card_finsetIntegerMultiple`

English:
theorem card_finsetIntegerMultiple
  given: [DecidableEq R] (s : Finset S)
  proof: (Finset.card_image_of_injective _ (integerMultiple_injective M s id injective_id)).trans
    Finset.card_attach

中文:
定理 card_finset整数egerMultiple
  条件: [DecidableEq R] (s : 有限集 S)
  证明: (Finset.card_image_of_injective _ (integerMultiple_injective M s id injective_id)).trans
    Finset.card_attach

Depends on / 依赖: Finset, Finset.card_attach, Finset.card_image_of_injective, card_attach, card_image_of_injective, injective_id, integerMultiple_injective
-/
theorem card_finsetIntegerMultiple [DecidableEq R] (s : Finset S) :
    (finsetIntegerMultiple M s).card = s.card :=
  (Finset.card_image_of_injective _ (integerMultiple_injective M s id injective_id)).trans
    Finset.card_attach

end IsLocalization
