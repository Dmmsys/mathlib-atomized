/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.LinearCombination

/-!

# Idempotents in rings

The predicate `IsIdempotentElem` is defined for general monoids in
`Mathlib/Algebra/Group/Idempotent.lean`; ring-specific lemmas are in
`Mathlib/Algebra/Ring/Idempotent.lean`.
In this file we provide various results regarding idempotent elements in rings.

## Main definitions

- `OrthogonalIdempotents`:
  A family `{ eᵢ }` of idempotent elements is orthogonal if `eᵢ * eⱼ = 0` for all `i ≠ j`.
- `CompleteOrthogonalIdempotents`:
  A family `{ eᵢ }` of orthogonal idempotent elements is complete if `∑ eᵢ = 1`.

## Main results

- `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`:
  If the kernel of `f : R →+* S` consists of nilpotent elements, and `{ eᵢ }` is a family of
  complete orthogonal idempotents in the range of `f`, then `{ eᵢ }` is the image of some
  complete orthogonal idempotents in `R`.
- `existsUnique_isIdempotentElem_eq_of_ker_isNilpotent`:
  If `R` is commutative and the kernel of `f : R →+* S` consists of nilpotent elements,
  then every idempotent in the range of `f` lifts to a unique idempotent in `R`.
- `CompleteOrthogonalIdempotents.bijective_pi`:
  If `R` is commutative, then a family `{ eᵢ }` of complete orthogonal idempotent elements induces
  a ring isomorphism `R ≃ ∏ R ⧸ ⟨1 - eᵢ⟩`.
-/

@[expose] public section

section Semiring

variable {R S : Type*} [Semiring R] [Semiring S] (f : R ->+* S)
variable {I : Type*} (e : I -> R)

/-- A family `{ eᵢ }` of idempotent elements is orthogonal if `eᵢ * eⱼ = 0` for all `i ≠ j`. -/
@[mk_iff]
/--
Definition of `OrthogonalIdempotents` / `OrthogonalIdempotents` 的定义

English:
structure OrthogonalIdempotents
  parameters: : Prop where
  axioms and operations (2):
    - idem : forall i, IsIdempotentElem (e i)
    - ortho : Pairwise (e · * e · = 0)

中文:
结构 正交幂等
  参数: : 命题 where
  公理与运算 (2 个):
    - idem : 对任意 i, IsIdempotentElem (e i)
    - ortho : 两两 (e · * e · = 0)
-/
structure OrthogonalIdempotents : Prop where
  idem : forall i, IsIdempotentElem (e i)
  ortho : Pairwise (e · * e · = 0)

variable {e}

/--
lemma `OrthogonalIdempotents.mul_eq` / 引理 `OrthogonalIdempotents.mul_eq`

English:
lemma OrthogonalIdempotents.mul_eq
  given: [DecidableEq I] (he : OrthogonalIdempotents e) (i j)
  proof: by
  split
  · simp [*, (he.idem j).eq]
  · exact he.ortho ‹_›

中文:
引理 正交幂等.mul_eq
  条件: [DecidableEq I] (he : 正交幂等 e) (i j)
  证明: by
  split
  · simp [*, (he.idem j).eq]
  · exact he.ortho ‹_›

Depends on / 依赖: he.idem, he.ortho
-/
lemma OrthogonalIdempotents.mul_eq [DecidableEq I] (he : OrthogonalIdempotents e) (i j) :
    e i * e j = if i = j then e i else 0 := by
  split
  · simp [*, (he.idem j).eq]
  · exact he.ortho ‹_›

/--
lemma `OrthogonalIdempotents.iff_mul_eq` / 引理 `OrthogonalIdempotents.iff_mul_eq`

English:
lemma OrthogonalIdempotents.iff_mul_eq
  given: [DecidableEq I]
  proof: ⟨mul_eq, fun H => ⟨fun i => by simpa using! H i i, fun i j e => by simpa [e] using! H i j⟩⟩

中文:
引理 正交幂等.iff_mul_eq
  条件: [DecidableEq I]
  证明: ⟨mul_eq, fun H => ⟨fun i => by simpa using! H i i, fun i j e => by simpa [e] using! H i j⟩⟩

Depends on / 依赖: mul_eq
-/
lemma OrthogonalIdempotents.iff_mul_eq [DecidableEq I] :
    OrthogonalIdempotents e ↔ forall i j, e i * e j = if i = j then e i else 0 :=
  ⟨mul_eq, fun H => ⟨fun i => by simpa using! H i i, fun i j e => by simpa [e] using! H i j⟩⟩

/--
lemma `OrthogonalIdempotents.isIdempotentElem_sum` / 引理 `OrthogonalIdempotents.isIdempotentElem_sum`

English:
lemma OrthogonalIdempotents.isIdempotentElem_sum
  given: (he : OrthogonalIdempotents e) {s : Finset I}
  proof: by
  classical
  simp [IsIdempotentElem, Finset.sum_mul, Finset.mul_sum, he.mul_eq]

中文:
引理 正交幂等.isIdempotentElem_sum
  条件: (he : 正交幂等 e) {s : 有限集 I}
  证明: by
  classical
  simp [IsIdempotentElem, Finset.sum_mul, Finset.mul_sum, he.mul_eq]

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_mul, IsIdempotentElem, classical, he.mul_eq, mul_eq, mul_sum, sum_mul
-/
lemma OrthogonalIdempotents.isIdempotentElem_sum (he : OrthogonalIdempotents e) {s : Finset I} :
    IsIdempotentElem (∑ i in s, e i) := by
  classical
  simp [IsIdempotentElem, Finset.sum_mul, Finset.mul_sum, he.mul_eq]

/--
lemma `OrthogonalIdempotents.mul_sum_of_mem` / 引理 `OrthogonalIdempotents.mul_sum_of_mem`

English:
lemma OrthogonalIdempotents.mul_sum_of_mem
  statement: (he : OrthogonalIdempotents e)
  proof: by
  classical
  simp [Finset.mul_sum, he.mul_eq, h]

中文:
引理 正交幂等.mul_sum_of_mem
  结论: (he : 正交幂等 e)
  证明: by
  classical
  simp [Finset.mul_sum, he.mul_eq, h]

Depends on / 依赖: Finset, Finset.mul_sum, classical, he.mul_eq, mul_eq, mul_sum
-/
lemma OrthogonalIdempotents.mul_sum_of_mem (he : OrthogonalIdempotents e)
    {i : I} {s : Finset I} (h : i in s) : e i * ∑ j in s, e j = e i := by
  classical
  simp [Finset.mul_sum, he.mul_eq, h]

/--
lemma `OrthogonalIdempotents.mul_sum_of_notMem` / 引理 `OrthogonalIdempotents.mul_sum_of_notMem`

English:
lemma OrthogonalIdempotents.mul_sum_of_notMem
  statement: (he : OrthogonalIdempotents e)
  proof: by
  classical
  simp [Finset.mul_sum, he.mul_eq, h]

中文:
引理 正交幂等.mul_sum_of_notMem
  结论: (he : 正交幂等 e)
  证明: by
  classical
  simp [Finset.mul_sum, he.mul_eq, h]

Depends on / 依赖: Finset, Finset.mul_sum, classical, he.mul_eq, mul_eq, mul_sum
-/
lemma OrthogonalIdempotents.mul_sum_of_notMem (he : OrthogonalIdempotents e)
    {i : I} {s : Finset I} (h : i ∉ s) : e i * ∑ j in s, e j = 0 := by
  classical
  simp [Finset.mul_sum, he.mul_eq, h]

/--
lemma `OrthogonalIdempotents.map` / 引理 `OrthogonalIdempotents.map`

English:
lemma OrthogonalIdempotents.map
  given: (he : OrthogonalIdempotents e)
  proof: by
  classical
  simp [iff_mul_eq, he.mul_eq, ← map_mul f, apply_ite f]

中文:
引理 正交幂等.map
  条件: (he : 正交幂等 e)
  证明: by
  classical
  simp [iff_mul_eq, he.mul_eq, ← map_mul f, apply_ite f]

Depends on / 依赖: apply_ite, classical, he.mul_eq, iff_mul_eq, map_mul, mul_eq
-/
lemma OrthogonalIdempotents.map (he : OrthogonalIdempotents e) :
    OrthogonalIdempotents (f ∘ e) := by
  classical
  simp [iff_mul_eq, he.mul_eq, ← map_mul f, apply_ite f]

/--
lemma `OrthogonalIdempotents.map_injective_iff` / 引理 `OrthogonalIdempotents.map_injective_iff`

English:
lemma OrthogonalIdempotents.map_injective_iff
  given: (hf : Function.Injective f)
  proof: by
  classical
  simp [iff_mul_eq, ← hf.eq_iff, apply_ite]

中文:
引理 正交幂等.map_injective_iff
  条件: (hf : 函数.单射 f)
  证明: by
  classical
  simp [iff_mul_eq, ← hf.eq_iff, apply_ite]

Depends on / 依赖: apply_ite, classical, eq_iff, hf.eq_iff, iff_mul_eq
-/
lemma OrthogonalIdempotents.map_injective_iff (hf : Function.Injective f) :
    OrthogonalIdempotents (f ∘ e) ↔ OrthogonalIdempotents e := by
  classical
  simp [iff_mul_eq, ← hf.eq_iff, apply_ite]

/--
lemma `OrthogonalIdempotents.embedding` / 引理 `OrthogonalIdempotents.embedding`

English:
lemma OrthogonalIdempotents.embedding
  given: (he : OrthogonalIdempotents e) {J} (i : J ↪ I)
  proof: by
  classical
  simp [iff_mul_eq, he.mul_eq]

中文:
引理 正交幂等.embedding
  条件: (he : 正交幂等 e) {J} (i : J ↪ I)
  证明: by
  classical
  simp [iff_mul_eq, he.mul_eq]

Depends on / 依赖: classical, he.mul_eq, iff_mul_eq, mul_eq
-/
lemma OrthogonalIdempotents.embedding (he : OrthogonalIdempotents e) {J} (i : J ↪ I) :
    OrthogonalIdempotents (e ∘ i) := by
  classical
  simp [iff_mul_eq, he.mul_eq]

/--
lemma `OrthogonalIdempotents.equiv` / 引理 `OrthogonalIdempotents.equiv`

English:
lemma OrthogonalIdempotents.equiv
  given: {J} (i : J ≃ I)
  proof: by
  classical
  simp [iff_mul_eq, i.forall_congr_left]

中文:
引理 正交幂等.equiv
  条件: {J} (i : J ≃ I)
  证明: by
  classical
  simp [iff_mul_eq, i.forall_congr_left]

Depends on / 依赖: classical, forall_congr_left, i.forall_congr_left, iff_mul_eq
-/
lemma OrthogonalIdempotents.equiv {J} (i : J ≃ I) :
    OrthogonalIdempotents (e ∘ i) ↔ OrthogonalIdempotents e := by
  classical
  simp [iff_mul_eq, i.forall_congr_left]

/--
lemma `OrthogonalIdempotents.unique` / 引理 `OrthogonalIdempotents.unique`

English:
lemma OrthogonalIdempotents.unique
  given: [Unique I]
  proof: by
  simp only [orthogonalIdempotents_iff, Unique.forall_iff, Subsingleton.pairwise, and_true]

中文:
引理 正交幂等.unique
  条件: [唯一 I]
  证明: by
  simp only [orthogonalIdempotents_iff, Unique.forall_iff, Subsingleton.pairwise, and_true]

Depends on / 依赖: Subsingleton, Subsingleton.pairwise, Unique, Unique.forall_iff, and_true, forall_iff, orthogonalIdempotents_iff, pairwise
-/
lemma OrthogonalIdempotents.unique [Unique I] :
    OrthogonalIdempotents e ↔ IsIdempotentElem (e default) := by
  simp only [orthogonalIdempotents_iff, Unique.forall_iff, Subsingleton.pairwise, and_true]

/--
lemma `OrthogonalIdempotents.option` / 引理 `OrthogonalIdempotents.option`

English:
lemma OrthogonalIdempotents.option
  statement: (he : OrthogonalIdempotents e) [Fintype I] (x)
  proof: i.rec hx he.idem
  ortho i j ne := by
    classical
    rcases i with - | i <;> rcases j with - | j
    · cases ne rfl
    · simpa only [mul_assoc, Finset.sum_mul, he.mul_eq, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, zero_mul] using! congr_arg (· * e j) hx₁
    · simpa only [Option.elim_some, Option.elim_none, ← mul_assoc, Finset.mul_sum, he.mul_eq,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_zero] using! congr_arg (e i * ·) hx₂
    · exact he.ortho (Option.some_inj.ne.mp ne)

中文:
引理 正交幂等.option
  结论: (he : 正交幂等 e) [有限类型 I] (x)
  证明: i.rec hx he.idem
  ortho i j ne := by
    classical
    rcases i with - | i <;> rcases j with - | j
    · cases ne rfl
    · simpa only [mul_assoc, Finset.sum_mul, he.mul_eq, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, zero_mul] using! congr_arg (· * e j) hx₁
    · simpa only [Option.elim_some, Option.elim_none, ← mul_assoc, Finset.mul_sum, he.mul_eq,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_zero] using! congr_arg (e i * ·) hx₂
    · exact he.ortho (Option.some_inj.ne.mp ne)

Depends on / 依赖: he.idem, i.rec
-/
lemma OrthogonalIdempotents.option (he : OrthogonalIdempotents e) [Fintype I] (x)
    (hx : IsIdempotentElem x) (hx₁ : x * ∑ i, e i = 0) (hx₂ : (∑ i, e i) * x = 0) :
    OrthogonalIdempotents (Option.elim · x e) where
  idem i := i.rec hx he.idem
  ortho i j ne := by
    classical
    rcases i with - | i <;> rcases j with - | j
    · cases ne rfl
    · simpa only [mul_assoc, Finset.sum_mul, he.mul_eq, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, zero_mul] using! congr_arg (· * e j) hx₁
    · simpa only [Option.elim_some, Option.elim_none, ← mul_assoc, Finset.mul_sum, he.mul_eq,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_zero] using! congr_arg (e i * ·) hx₂
    · exact he.ortho (Option.some_inj.ne.mp ne)

variable [Fintype I]

/--
A family `{ eᵢ }` of idempotent elements is complete orthogonal if
1. (orthogonal) `eᵢ * eⱼ = 0` for all `i ≠ j`.
2. (complete) `∑ eᵢ = 1`
-/
@[mk_iff]
/--
Definition of `CompleteOrthogonalIdempotents` / `CompleteOrthogonalIdempotents` 的定义

English:
structure CompleteOrthogonalIdempotents
  parameters: (e : I -> R)
  extends: OrthogonalIdempotents e
  axioms and operations (1):
    - complete : ∑ i, e i = 1

中文:
结构 余mpleteOrthogonalIdempotents
  参数: (e : I -> R)
  继承: 正交幂等 e
  公理与运算 (1 个):
    - complete : ∑ i, e i = 1
-/
structure CompleteOrthogonalIdempotents (e : I -> R) : Prop extends OrthogonalIdempotents e where
  complete : ∑ i, e i = 1

/--
lemma `CompleteOrthogonalIdempotents.iff_ortho_complete` / 引理 `CompleteOrthogonalIdempotents.iff_ortho_complete`

English:
lemma CompleteOrthogonalIdempotents.iff_ortho_complete
  proof: by
  rw [completeOrthogonalIdempotents_iff]; rw [orthogonalIdempotents_iff]; rw [and_assoc]; rw [and_iff_right_of_imp]
  intro ⟨ortho, complete⟩ i
  apply_fun (e i * ·) at complete
  rwa [Finset.mul_sum, Finset.sum_eq_single i (fun _ _ ne => ortho ne.symm) (by simp at ·), mul_one]
    at complete

中文:
引理 余mpleteOrthogonalIdempotents.iff_ortho_complete
  证明: by
  rw [completeOrthogonalIdempotents_iff]; rw [orthogonalIdempotents_iff]; rw [and_assoc]; rw [and_iff_right_of_imp]
  intro ⟨ortho, complete⟩ i
  apply_fun (e i * ·) at complete
  rwa [Finset.mul_sum, Finset.sum_eq_single i (fun _ _ ne => ortho ne.symm) (by simp at ·), mul_one]
    at complete

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_eq_single, and_assoc, and_iff_right_of_imp, apply_fun, complete, completeOrthogonalIdempotents_iff, mul_one, mul_sum, ne.symm, orthogonalIdempotents_iff, sum_eq_single
-/
lemma CompleteOrthogonalIdempotents.iff_ortho_complete :
    CompleteOrthogonalIdempotents e ↔ Pairwise (e · * e · = 0) ∧ ∑ i, e i = 1 := by
  rw [completeOrthogonalIdempotents_iff]; rw [orthogonalIdempotents_iff]; rw [and_assoc]; rw [and_iff_right_of_imp]
  intro ⟨ortho, complete⟩ i
  apply_fun (e i * ·) at complete
  rwa [Finset.mul_sum, Finset.sum_eq_single i (fun _ _ ne => ortho ne.symm) (by simp at ·), mul_one]
    at complete

/--
lemma `CompleteOrthogonalIdempotents.pair_iff'ₛ` / 引理 `CompleteOrthogonalIdempotents.pair_iff'ₛ`

English:
lemma CompleteOrthogonalIdempotents.pair_iff'ₛ
  given: {x y : R}
  proof: by
  simp [iff_ortho_complete, Pairwise, Fin.forall_fin_two, and_assoc]

中文:
引理 余mpleteOrthogonalIdempotents.pair_iff'ₛ
  条件: {x y : R}
  证明: by
  simp [iff_ortho_complete, Pairwise, Fin.forall_fin_two, and_assoc]

Depends on / 依赖: Fin.forall_fin_two, Pairwise, and_assoc, forall_fin_two, iff_ortho_complete
-/
lemma CompleteOrthogonalIdempotents.pair_iff'ₛ {x y : R} :
    CompleteOrthogonalIdempotents ![x, y] ↔ x * y = 0 ∧ y * x = 0 ∧ x + y = 1 := by
  simp [iff_ortho_complete, Pairwise, Fin.forall_fin_two, and_assoc]

/--
lemma `CompleteOrthogonalIdempotents.pair_iffₛ` / 引理 `CompleteOrthogonalIdempotents.pair_iffₛ`

English:
lemma CompleteOrthogonalIdempotents.pair_iffₛ
  given: {R} [CommSemiring R] {x y : R}
  proof: by
  rw [pair_iff'ₛ]; rw [and_left_comm]; rw [and_iff_right_of_imp]; exact (mul_comm x y ▸ ·.1)

中文:
引理 余mpleteOrthogonalIdempotents.pair_iffₛ
  条件: {R} [交换半环 R] {x y : R}
  证明: by
  rw [pair_iff'ₛ]; rw [and_left_comm]; rw [and_iff_right_of_imp]; exact (mul_comm x y ▸ ·.1)

Depends on / 依赖: and_iff_right_of_imp, and_left_comm, mul_comm, pair_iff
-/
lemma CompleteOrthogonalIdempotents.pair_iffₛ {R} [CommSemiring R] {x y : R} :
    CompleteOrthogonalIdempotents ![x, y] ↔ x * y = 0 ∧ x + y = 1 := by
  rw [pair_iff'ₛ]; rw [and_left_comm]; rw [and_iff_right_of_imp]; exact (mul_comm x y ▸ ·.1)

/--
lemma `CompleteOrthogonalIdempotents.unique_iff` / 引理 `CompleteOrthogonalIdempotents.unique_iff`

English:
lemma CompleteOrthogonalIdempotents.unique_iff
  given: [Unique I]
  proof: by
  rw [completeOrthogonalIdempotents_iff]; rw [OrthogonalIdempotents.unique]; rw [Fintype.sum_unique]; rw [and_iff_right_iff_imp]
  exact (· ▸ IsIdempotentElem.one)

中文:
引理 余mpleteOrthogonalIdempotents.unique_iff
  条件: [唯一 I]
  证明: by
  rw [completeOrthogonalIdempotents_iff]; rw [OrthogonalIdempotents.unique]; rw [Fintype.sum_unique]; rw [and_iff_right_iff_imp]
  exact (· ▸ IsIdempotentElem.one)

Depends on / 依赖: Fintype, Fintype.sum_unique, IsIdempotentElem, IsIdempotentElem.one, OrthogonalIdempotents, OrthogonalIdempotents.unique, and_iff_right_iff_imp, completeOrthogonalIdempotents_iff, sum_unique, unique
-/
lemma CompleteOrthogonalIdempotents.unique_iff [Unique I] :
    CompleteOrthogonalIdempotents e ↔ e default = 1 := by
  rw [completeOrthogonalIdempotents_iff]; rw [OrthogonalIdempotents.unique]; rw [Fintype.sum_unique]; rw [and_iff_right_iff_imp]
  exact (· ▸ IsIdempotentElem.one)

/--
lemma `CompleteOrthogonalIdempotents.single` / 引理 `CompleteOrthogonalIdempotents.single`

English:
lemma CompleteOrthogonalIdempotents.single
  statement: {I : Type*} [Fintype I] [DecidableEq I]
  proof: by
  refine ⟨⟨by simp [IsIdempotentElem, ← Pi.single_mul], ?_⟩, Finset.univ_sum_single 1⟩
  intro i j hij
  ext k
  by_cases hi : i = k
  · subst hi; simp [hij]
  · simp [hi]

中文:
引理 余mpleteOrthogonalIdempotents.single
  结论: {I : 类型} [有限类型 I] [DecidableEq I]
  证明: by
  refine ⟨⟨by simp [IsIdempotentElem, ← Pi.single_mul], ?_⟩, Finset.univ_sum_single 1⟩
  intro i j hij
  ext k
  by_cases hi : i = k
  · subst hi; simp [hij]
  · simp [hi]

Depends on / 依赖: Finset, Finset.univ_sum_single, IsIdempotentElem, Pi.single_mul, single_mul, univ_sum_single
-/
lemma CompleteOrthogonalIdempotents.single {I : Type*} [Fintype I] [DecidableEq I]
    (R : I -> Type*) [forall i, Semiring (R i)] :
    CompleteOrthogonalIdempotents (Pi.single (M := R) · 1) := by
  refine ⟨⟨by simp [IsIdempotentElem, ← Pi.single_mul], ?_⟩, Finset.univ_sum_single 1⟩
  intro i j hij
  ext k
  by_cases hi : i = k
  · subst hi; simp [hij]
  · simp [hi]

/--
lemma `CompleteOrthogonalIdempotents.map` / 引理 `CompleteOrthogonalIdempotents.map`

English:
lemma CompleteOrthogonalIdempotents.map
  given: (he : CompleteOrthogonalIdempotents e)
  proof: he.toOrthogonalIdempotents.map f
  complete := by simp only [Function.comp_apply, ← map_sum, he.complete, map_one]

中文:
引理 余mpleteOrthogonalIdempotents.map
  条件: (he : 余mpleteOrthogonalIdempotents e)
  证明: he.toOrthogonalIdempotents.map f
  complete := by simp only [Function.comp_apply, ← map_sum, he.complete, map_one]

Depends on / 依赖: he.toOrthogonalIdempotents.map, toOrthogonalIdempotents
-/
lemma CompleteOrthogonalIdempotents.map (he : CompleteOrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (f ∘ e) where
  __ := he.toOrthogonalIdempotents.map f
  complete := by simp only [Function.comp_apply, ← map_sum, he.complete, map_one]

/--
lemma `CompleteOrthogonalIdempotents.map_injective_iff` / 引理 `CompleteOrthogonalIdempotents.map_injective_iff`

English:
lemma CompleteOrthogonalIdempotents.map_injective_iff
  given: (hf : Function.Injective f)
  proof: by
  simp [completeOrthogonalIdempotents_iff, ← hf.eq_iff,
    OrthogonalIdempotents.map_injective_iff f hf]

中文:
引理 余mpleteOrthogonalIdempotents.map_injective_iff
  条件: (hf : 函数.单射 f)
  证明: by
  simp [completeOrthogonalIdempotents_iff, ← hf.eq_iff,
    OrthogonalIdempotents.map_injective_iff f hf]

Depends on / 依赖: OrthogonalIdempotents, OrthogonalIdempotents.map_injective_iff, completeOrthogonalIdempotents_iff, eq_iff, hf.eq_iff, map_injective_iff
-/
lemma CompleteOrthogonalIdempotents.map_injective_iff (hf : Function.Injective f) :
    CompleteOrthogonalIdempotents (f ∘ e) ↔ CompleteOrthogonalIdempotents e := by
  simp [completeOrthogonalIdempotents_iff, ← hf.eq_iff,
    OrthogonalIdempotents.map_injective_iff f hf]

/--
lemma `CompleteOrthogonalIdempotents.equiv` / 引理 `CompleteOrthogonalIdempotents.equiv`

English:
lemma CompleteOrthogonalIdempotents.equiv
  given: {J} [Fintype J] (i : J ≃ I)
  proof: by
  simp only [completeOrthogonalIdempotents_iff, OrthogonalIdempotents.equiv, Function.comp_apply,
    Fintype.sum_equiv i _ e (fun _ => rfl)]

@[nontriviality]

中文:
引理 余mpleteOrthogonalIdempotents.equiv
  条件: {J} [有限类型 J] (i : J ≃ I)
  证明: by
  simp only [completeOrthogonalIdempotents_iff, OrthogonalIdempotents.equiv, Function.comp_apply,
    Fintype.sum_equiv i _ e (fun _ => rfl)]

@[nontriviality]

Depends on / 依赖: Fintype, Fintype.sum_equiv, Function, Function.comp_apply, OrthogonalIdempotents, OrthogonalIdempotents.equiv, comp_apply, completeOrthogonalIdempotents_iff, sum_equiv
-/
lemma CompleteOrthogonalIdempotents.equiv {J} [Fintype J] (i : J ≃ I) :
    CompleteOrthogonalIdempotents (e ∘ i) ↔ CompleteOrthogonalIdempotents e := by
  simp only [completeOrthogonalIdempotents_iff, OrthogonalIdempotents.equiv, Function.comp_apply,
    Fintype.sum_equiv i _ e (fun _ => rfl)]

@[nontriviality]
/--
lemma `CompleteOrthogonalIdempotents.of_subsingleton` / 引理 `CompleteOrthogonalIdempotents.of_subsingleton`

English:
lemma CompleteOrthogonalIdempotents.of_subsingleton
  given: [Subsingleton R]
  proof: ⟨⟨fun _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩, Subsingleton.elim _ _⟩

中文:
引理 余mpleteOrthogonalIdempotents.of_subsingleton
  条件: [子单例 R]
  证明: ⟨⟨fun _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩, Subsingleton.elim _ _⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
lemma CompleteOrthogonalIdempotents.of_subsingleton [Subsingleton R] :
    CompleteOrthogonalIdempotents e :=
  ⟨⟨fun _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩, Subsingleton.elim _ _⟩

end Semiring

section Ring

variable {R S : Type*} [Ring R] [Ring S] (f : R ->+* S)

/--
theorem `isIdempotentElem_one_sub_one_sub_pow_pow` / 定理 `isIdempotentElem_one_sub_one_sub_pow_pow`

English:
theorem isIdempotentElem_one_sub_one_sub_pow_pow
  proof: by
  have : (x - x ^ 2) ^ n ∣ (1 - (1 - x ^ n) ^ n) - (1 - (1 - x ^ n) ^ n) ^ 2 := by
    conv_rhs => rw [pow_two, ← mul_one_sub, sub_sub_cancel]
    nth_rw 1 3 [← one_pow n]
    rw [← (Commute.one_left x).mul_geom_sum₂]; rw [← (Commute.one_left (1 - x ^ n)).mul_geom_sum₂]
    simp only [sub_sub_cancel, one_pow, one_mul]
    rw [Commute.mul_pow]; rw [Commute.mul_mul_mul_comm]; rw [← Commute.mul_pow]; rw [mul_one_sub]; rw [← pow_two]
    · exact ⟨_, rfl⟩
    · simp
    · refine .pow_right (.sub_right (.one_right _) (.sum_left _ _ _ fun _ _ => .pow_left ?_ _)) _
      simp
    · exact .sub_left (.one_left _) (.sum_right _ _ _ fun _ _ => .pow_right rfl _)
  rwa [hx, zero_dvd_iff, sub_eq_zero, eq_comm, pow_two] at this

中文:
定理 isIdempotentElem_one_sub_one_sub_pow_pow
  证明: by
  have : (x - x ^ 2) ^ n ∣ (1 - (1 - x ^ n) ^ n) - (1 - (1 - x ^ n) ^ n) ^ 2 := by
    conv_rhs => rw [pow_two, ← mul_one_sub, sub_sub_cancel]
    nth_rw 1 3 [← one_pow n]
    rw [← (Commute.one_left x).mul_geom_sum₂]; rw [← (Commute.one_left (1 - x ^ n)).mul_geom_sum₂]
    simp only [sub_sub_cancel, one_pow, one_mul]
    rw [Commute.mul_pow]; rw [Commute.mul_mul_mul_comm]; rw [← Commute.mul_pow]; rw [mul_one_sub]; rw [← pow_two]
    · exact ⟨_, rfl⟩
    · simp
    · refine .pow_right (.sub_right (.one_right _) (.sum_left _ _ _ fun _ _ => .pow_left ?_ _)) _
      simp
    · exact .sub_left (.one_left _) (.sum_right _ _ _ fun _ _ => .pow_right rfl _)
  rwa [hx, zero_dvd_iff, sub_eq_zero, eq_comm, pow_two] at this

Depends on / 依赖: Commute, Commute.mul_mul_mul_comm, Commute.mul_pow, Commute.one_left, conv_rhs, mul_mul_mul_comm, mul_one_sub, mul_pow, nth_rw, one_left, one_mul, one_pow, one_right, pow_right, pow_two, sub_right, sub_sub_cancel, sum_left
-/
theorem isIdempotentElem_one_sub_one_sub_pow_pow
    (x : R) (n : Nat) (hx : (x - x ^ 2) ^ n = 0) :
    IsIdempotentElem (1 - (1 - x ^ n) ^ n) := by
  have : (x - x ^ 2) ^ n ∣ (1 - (1 - x ^ n) ^ n) - (1 - (1 - x ^ n) ^ n) ^ 2 := by
    conv_rhs => rw [pow_two, ← mul_one_sub, sub_sub_cancel]
    nth_rw 1 3 [← one_pow n]
    rw [← (Commute.one_left x).mul_geom_sum₂]; rw [← (Commute.one_left (1 - x ^ n)).mul_geom_sum₂]
    simp only [sub_sub_cancel, one_pow, one_mul]
    rw [Commute.mul_pow]; rw [Commute.mul_mul_mul_comm]; rw [← Commute.mul_pow]; rw [mul_one_sub]; rw [← pow_two]
    · exact ⟨_, rfl⟩
    · simp
    · refine .pow_right (.sub_right (.one_right _) (.sum_left _ _ _ fun _ _ => .pow_left ?_ _)) _
      simp
    · exact .sub_left (.one_left _) (.sum_right _ _ _ fun _ _ => .pow_right rfl _)
  rwa [hx, zero_dvd_iff, sub_eq_zero, eq_comm, pow_two] at this

/--
theorem `exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux` / 定理 `exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux`

English:
theorem exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux
  proof: by
  obtain ⟨e₁, rfl⟩ := he
  cases subsingleton_or_nontrivial R
  · exact ⟨_, Subsingleton.elim _ _, rfl, Subsingleton.elim _ _⟩
  let a := e₁ - e₁ * e₂
  have ha : f a = f e₁ := by rw [map_sub, map_mul, he₁e₂, sub_zero]
  have ha' : a * e₂ = 0 := by rw [sub_mul, mul_assoc, he₂.eq, sub_self]
  have hx' : a - a ^ 2 in RingHom.ker f := by
    simp [RingHom.mem_ker, pow_two, ha, he₁.eq]
  obtain ⟨n, hn⟩ := h _ hx'
  refine ⟨_, isIdempotentElem_one_sub_one_sub_pow_pow _ _ hn, ?_, ?_⟩
  · rcases n with - | n
    · simp at hn
    simp only [map_sub, map_one, map_pow, ha, he₁.pow_succ_eq,
      he₁.one_sub.pow_succ_eq, sub_sub_cancel]
  · obtain ⟨k, hk⟩ := (Commute.one_left (MulOpposite.op <| 1 - a ^ n)).sub_dvd_pow_sub_pow n
    apply_fun MulOpposite.unop at hk
    have : 1 - (1 - a ^ n) ^ n = MulOpposite.unop k * a ^ n := by simpa using hk
    rw [this]; rw [mul_assoc]
    rcases n with - | n
    · simp at hn
    rw [pow_succ]; rw [mul_assoc]; rw [ha']; rw [mul_zero]; rw [mul_zero]

中文:
定理 存在_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux
  证明: by
  obtain ⟨e₁, rfl⟩ := he
  cases subsingleton_or_nontrivial R
  · exact ⟨_, Subsingleton.elim _ _, rfl, Subsingleton.elim _ _⟩
  let a := e₁ - e₁ * e₂
  have ha : f a = f e₁ := by rw [map_sub, map_mul, he₁e₂, sub_zero]
  have ha' : a * e₂ = 0 := by rw [sub_mul, mul_assoc, he₂.eq, sub_self]
  have hx' : a - a ^ 2 in RingHom.ker f := by
    simp [RingHom.mem_ker, pow_two, ha, he₁.eq]
  obtain ⟨n, hn⟩ := h _ hx'
  refine ⟨_, isIdempotentElem_one_sub_one_sub_pow_pow _ _ hn, ?_, ?_⟩
  · rcases n with - | n
    · simp at hn
    simp only [map_sub, map_one, map_pow, ha, he₁.pow_succ_eq,
      he₁.one_sub.pow_succ_eq, sub_sub_cancel]
  · obtain ⟨k, hk⟩ := (Commute.one_left (MulOpposite.op <| 1 - a ^ n)).sub_dvd_pow_sub_pow n
    apply_fun MulOpposite.unop at hk
    have : 1 - (1 - a ^ n) ^ n = MulOpposite.unop k * a ^ n := by simpa using hk
    rw [this]; rw [mul_assoc]
    rcases n with - | n
    · simp at hn
    rw [pow_succ]; rw [mul_assoc]; rw [ha']; rw [mul_zero]; rw [mul_zero]

Depends on / 依赖: RingHom, RingHom.ker, RingHom.mem_ker, Subsingleton, Subsingleton.elim, isIdempotentElem_one_sub_one_sub_pow_pow, map_mul, map_sub, mem_ker, mul_assoc, pow_two, sub_mul, sub_self, sub_zero, subsingleton_or_nontrivial
-/
theorem exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux
    (h : forall x in RingHom.ker f, IsNilpotent x)
    (e₁ : S) (he : e₁ in f.range) (he₁ : IsIdempotentElem e₁)
    (e₂ : R) (he₂ : IsIdempotentElem e₂) (he₁e₂ : e₁ * f e₂ = 0) :
    exists e' : R, IsIdempotentElem e' ∧ f e' = e₁ ∧ e' * e₂ = 0 := by
  obtain ⟨e₁, rfl⟩ := he
  cases subsingleton_or_nontrivial R
  · exact ⟨_, Subsingleton.elim _ _, rfl, Subsingleton.elim _ _⟩
  let a := e₁ - e₁ * e₂
  have ha : f a = f e₁ := by rw [map_sub, map_mul, he₁e₂, sub_zero]
  have ha' : a * e₂ = 0 := by rw [sub_mul, mul_assoc, he₂.eq, sub_self]
  have hx' : a - a ^ 2 in RingHom.ker f := by
    simp [RingHom.mem_ker, pow_two, ha, he₁.eq]
  obtain ⟨n, hn⟩ := h _ hx'
  refine ⟨_, isIdempotentElem_one_sub_one_sub_pow_pow _ _ hn, ?_, ?_⟩
  · rcases n with - | n
    · simp at hn
    simp only [map_sub, map_one, map_pow, ha, he₁.pow_succ_eq,
      he₁.one_sub.pow_succ_eq, sub_sub_cancel]
  · obtain ⟨k, hk⟩ := (Commute.one_left (MulOpposite.op <| 1 - a ^ n)).sub_dvd_pow_sub_pow n
    apply_fun MulOpposite.unop at hk
    have : 1 - (1 - a ^ n) ^ n = MulOpposite.unop k * a ^ n := by simpa using hk
    rw [this]; rw [mul_assoc]
    rcases n with - | n
    · simp at hn
    rw [pow_succ]; rw [mul_assoc]; rw [ha']; rw [mul_zero]; rw [mul_zero]

/--
theorem `exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent` / 定理 `exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent`

English:
theorem exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent
  proof: by
  obtain ⟨e', h₁, rfl, h₂⟩ := exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux
    f h e₁ he he₁ e₂ he₂ he₁e₂
  refine ⟨(1 - e₂) * e', ?_, ?_, ?_, ?_⟩
  · rw [IsIdempotentElem, mul_assoc, ← mul_assoc e', mul_sub, mul_one, h₂, sub_zero, h₁.eq]
  · rw [map_mul, map_sub, map_one, sub_mul, one_mul, he₂e₁, sub_zero]
  · rw [mul_assoc, h₂, mul_zero]
  · rw [← mul_assoc, mul_sub, mul_one, he₂.eq, sub_self, zero_mul]

中文:
定理 存在_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent
  证明: by
  obtain ⟨e', h₁, rfl, h₂⟩ := exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux
    f h e₁ he he₁ e₂ he₂ he₁e₂
  refine ⟨(1 - e₂) * e', ?_, ?_, ?_, ?_⟩
  · rw [IsIdempotentElem, mul_assoc, ← mul_assoc e', mul_sub, mul_one, h₂, sub_zero, h₁.eq]
  · rw [map_mul, map_sub, map_one, sub_mul, one_mul, he₂e₁, sub_zero]
  · rw [mul_assoc, h₂, mul_zero]
  · rw [← mul_assoc, mul_sub, mul_one, he₂.eq, sub_self, zero_mul]

Depends on / 依赖: IsIdempotentElem, exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux, map_mul, map_one, map_sub, mul_assoc, mul_one, mul_sub, mul_zero, one_mul, sub_mul, sub_self, sub_zero, zero_mul
-/
theorem exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent
    (h : forall x in RingHom.ker f, IsNilpotent x)
    (e₁ : S) (he : e₁ in f.range) (he₁ : IsIdempotentElem e₁)
    (e₂ : R) (he₂ : IsIdempotentElem e₂) (he₁e₂ : e₁ * f e₂ = 0) (he₂e₁ : f e₂ * e₁ = 0) :
    exists e' : R, IsIdempotentElem e' ∧ f e' = e₁ ∧ e' * e₂ = 0 ∧ e₂ * e' = 0 := by
  obtain ⟨e', h₁, rfl, h₂⟩ := exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux
    f h e₁ he he₁ e₂ he₂ he₁e₂
  refine ⟨(1 - e₂) * e', ?_, ?_, ?_, ?_⟩
  · rw [IsIdempotentElem, mul_assoc, ← mul_assoc e', mul_sub, mul_one, h₂, sub_zero, h₁.eq]
  · rw [map_mul, map_sub, map_one, sub_mul, one_mul, he₂e₁, sub_zero]
  · rw [mul_assoc, h₂, mul_zero]
  · rw [← mul_assoc, mul_sub, mul_one, he₂.eq, sub_self, zero_mul]

/--
theorem `exists_isIdempotentElem_eq_of_ker_isNilpotent` / 定理 `exists_isIdempotentElem_eq_of_ker_isNilpotent`

English:
theorem exists_isIdempotentElem_eq_of_ker_isNilpotent
  statement: (h : forall x in RingHom.ker f, IsNilpotent x)
  proof: by
  simpa using exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent f h e he he' 0 .zero (by simp)

中文:
定理 存在_isIdempotentElem_eq_of_ker_isNilpotent
  结论: (h : 对任意 x in 环态射.ker f, 是幂零 x)
  证明: by
  simpa using exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent f h e he he' 0 .zero (by simp)

Depends on / 依赖: exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent
-/
theorem exists_isIdempotentElem_eq_of_ker_isNilpotent (h : forall x in RingHom.ker f, IsNilpotent x)
    (e : S) (he : e in f.range) (he' : IsIdempotentElem e) :
    exists e' : R, IsIdempotentElem e' ∧ f e' = e := by
  simpa using exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent f h e he he' 0 .zero (by simp)

/--
lemma `OrthogonalIdempotents.lift_of_isNilpotent_ker_aux` / 引理 `OrthogonalIdempotents.lift_of_isNilpotent_ker_aux`

English:
lemma OrthogonalIdempotents.lift_of_isNilpotent_ker_aux
  proof: by
  induction n with
  | zero => refine ⟨0, ⟨finZeroElim, finZeroElim⟩, funext finZeroElim⟩
  | succ n IH =>
    obtain ⟨e', h₁, h₂⟩ := IH (he.embedding (Fin.succEmb n)) (fun i => he' _)
    have h₂' (i) : f (e' i) = e i.succ := congr_fun h₂ i
    obtain ⟨e₀, h₃, h₄, h₅, h₆⟩ :=
      exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent f h _ (he' 0) (he.idem 0) _
      h₁.isIdempotentElem_sum
      (by simp [Finset.mul_sum, h₂', he.mul_eq, eq_comm])
      (by simp [Finset.sum_mul, h₂', he.mul_eq])
    refine ⟨_, (h₁.option _ h₃ h₅ h₆).embedding (finSuccEquiv n).toEmbedding, funext fun i => ?_⟩
    obtain ⟨_ | i, rfl⟩ := (finSuccEquiv n).symm.surjective i <;> simp [*]

中文:
引理 正交幂等.lift_of_isNilpotent_ker_aux
  证明: by
  induction n with
  | zero => refine ⟨0, ⟨finZeroElim, finZeroElim⟩, funext finZeroElim⟩
  | succ n IH =>
    obtain ⟨e', h₁, h₂⟩ := IH (he.embedding (Fin.succEmb n)) (fun i => he' _)
    have h₂' (i) : f (e' i) = e i.succ := congr_fun h₂ i
    obtain ⟨e₀, h₃, h₄, h₅, h₆⟩ :=
      exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent f h _ (he' 0) (he.idem 0) _
      h₁.isIdempotentElem_sum
      (by simp [Finset.mul_sum, h₂', he.mul_eq, eq_comm])
      (by simp [Finset.sum_mul, h₂', he.mul_eq])
    refine ⟨_, (h₁.option _ h₃ h₅ h₆).embedding (finSuccEquiv n).toEmbedding, funext fun i => ?_⟩
    obtain ⟨_ | i, rfl⟩ := (finSuccEquiv n).symm.surjective i <;> simp [*]

Depends on / 依赖: Fin.succEmb, Finset, Finset.mul_sum, Finset.sum_mul, congr_fun, embedding, eq_comm, exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent, finZeroElim, he.embedding, he.idem, he.mul_eq, i.succ, isIdempotentElem_sum, mul_eq, mul_sum, option, succEmb, sum_mul
-/
lemma OrthogonalIdempotents.lift_of_isNilpotent_ker_aux
    (h : forall x in RingHom.ker f, IsNilpotent x)
    {n} {e : Fin n -> S} (he : OrthogonalIdempotents e) (he' : forall i, e i in f.range) :
    exists e' : Fin n -> R, OrthogonalIdempotents e' ∧ f ∘ e' = e := by
  induction n with
  | zero => refine ⟨0, ⟨finZeroElim, finZeroElim⟩, funext finZeroElim⟩
  | succ n IH =>
    obtain ⟨e', h₁, h₂⟩ := IH (he.embedding (Fin.succEmb n)) (fun i => he' _)
    have h₂' (i) : f (e' i) = e i.succ := congr_fun h₂ i
    obtain ⟨e₀, h₃, h₄, h₅, h₆⟩ :=
      exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent f h _ (he' 0) (he.idem 0) _
      h₁.isIdempotentElem_sum
      (by simp [Finset.mul_sum, h₂', he.mul_eq, eq_comm])
      (by simp [Finset.sum_mul, h₂', he.mul_eq])
    refine ⟨_, (h₁.option _ h₃ h₅ h₆).embedding (finSuccEquiv n).toEmbedding, funext fun i => ?_⟩
    obtain ⟨_ | i, rfl⟩ := (finSuccEquiv n).symm.surjective i <;> simp [*]

variable {I : Type*} {e : I -> R}

/--
lemma `OrthogonalIdempotents.lift_of_isNilpotent_ker` / 引理 `OrthogonalIdempotents.lift_of_isNilpotent_ker`

English:
lemma OrthogonalIdempotents.lift_of_isNilpotent_ker
  statement: [Finite I]
  proof: by
  cases nonempty_fintype I
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker_aux f h
    (he.embedding (Fintype.equivFin I).symm.toEmbedding) (fun _ => he' _)
  refine ⟨_, h₁.embedding (Fintype.equivFin I).toEmbedding,
    by ext x; simpa using congr_fun h₂ (Fintype.equivFin I x)⟩

中文:
引理 正交幂等.lift_of_isNilpotent_ker
  结论: [有限 I]
  证明: by
  cases nonempty_fintype I
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker_aux f h
    (he.embedding (Fintype.equivFin I).symm.toEmbedding) (fun _ => he' _)
  refine ⟨_, h₁.embedding (Fintype.equivFin I).toEmbedding,
    by ext x; simpa using congr_fun h₂ (Fintype.equivFin I x)⟩

Depends on / 依赖: Fintype, Fintype.equivFin, congr_fun, embedding, equivFin, he.embedding, lift_of_isNilpotent_ker_aux, nonempty_fintype, symm.toEmbedding, toEmbedding
-/
lemma OrthogonalIdempotents.lift_of_isNilpotent_ker [Finite I]
    (h : forall x in RingHom.ker f, IsNilpotent x)
    {e : I -> S} (he : OrthogonalIdempotents e) (he' : forall i, e i in f.range) :
    exists e' : I -> R, OrthogonalIdempotents e' ∧ f ∘ e' = e := by
  cases nonempty_fintype I
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker_aux f h
    (he.embedding (Fintype.equivFin I).symm.toEmbedding) (fun _ => he' _)
  refine ⟨_, h₁.embedding (Fintype.equivFin I).toEmbedding,
    by ext x; simpa using congr_fun h₂ (Fintype.equivFin I x)⟩

/--
lemma `CompleteOrthogonalIdempotents.pair_iff` / 引理 `CompleteOrthogonalIdempotents.pair_iff`

English:
lemma CompleteOrthogonalIdempotents.pair_iff
  given: {x y : R}
  proof: by
  rw [pair_iff'ₛ]; rw [← eq_sub_iff_add_eq']; rw [← and_assoc]; rw [and_congr_left_iff]
  rintro rfl
  simp [mul_sub, sub_mul, IsIdempotentElem, sub_eq_zero, eq_comm]

中文:
引理 余mpleteOrthogonalIdempotents.pair_iff
  条件: {x y : R}
  证明: by
  rw [pair_iff'ₛ]; rw [← eq_sub_iff_add_eq']; rw [← and_assoc]; rw [and_congr_left_iff]
  rintro rfl
  simp [mul_sub, sub_mul, IsIdempotentElem, sub_eq_zero, eq_comm]

Depends on / 依赖: IsIdempotentElem, and_assoc, and_congr_left_iff, eq_comm, eq_sub_iff_add_eq, mul_sub, pair_iff, sub_eq_zero, sub_mul
-/
lemma CompleteOrthogonalIdempotents.pair_iff {x y : R} :
    CompleteOrthogonalIdempotents ![x, y] ↔ IsIdempotentElem x ∧ y = 1 - x := by
  rw [pair_iff'ₛ]; rw [← eq_sub_iff_add_eq']; rw [← and_assoc]; rw [and_congr_left_iff]
  rintro rfl
  simp [mul_sub, sub_mul, IsIdempotentElem, sub_eq_zero, eq_comm]

/--
lemma `CompleteOrthogonalIdempotents.of_isIdempotentElem` / 引理 `CompleteOrthogonalIdempotents.of_isIdempotentElem`

English:
lemma CompleteOrthogonalIdempotents.of_isIdempotentElem
  given: {e : R} (he : IsIdempotentElem e)
  proof: pair_iff.mpr ⟨he, rfl⟩

中文:
引理 余mpleteOrthogonalIdempotents.of_isIdempotentElem
  条件: {e : R} (he : IsIdempotentElem e)
  证明: pair_iff.mpr ⟨he, rfl⟩

Depends on / 依赖: pair_iff, pair_iff.mpr
-/
lemma CompleteOrthogonalIdempotents.of_isIdempotentElem {e : R} (he : IsIdempotentElem e) :
    CompleteOrthogonalIdempotents ![e, 1 - e] :=
  pair_iff.mpr ⟨he, rfl⟩

variable [Fintype I]

/--
lemma `CompleteOrthogonalIdempotents.option` / 引理 `CompleteOrthogonalIdempotents.option`

English:
lemma CompleteOrthogonalIdempotents.option
  given: (he : OrthogonalIdempotents e)
  proof: he.option _ he.isIdempotentElem_sum.one_sub
    (by simp [sub_mul, he.isIdempotentElem_sum.eq]) (by simp [mul_sub, he.isIdempotentElem_sum.eq])
  complete := by
    rw [Fintype.sum_option]
    exact sub_add_cancel _ _

中文:
引理 余mpleteOrthogonalIdempotents.option
  条件: (he : 正交幂等 e)
  证明: he.option _ he.isIdempotentElem_sum.one_sub
    (by simp [sub_mul, he.isIdempotentElem_sum.eq]) (by simp [mul_sub, he.isIdempotentElem_sum.eq])
  complete := by
    rw [Fintype.sum_option]
    exact sub_add_cancel _ _

Depends on / 依赖: he.isIdempotentElem_sum.one_sub, he.option, isIdempotentElem_sum, one_sub, option
-/
lemma CompleteOrthogonalIdempotents.option (he : OrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (Option.elim · (1 - ∑ i, e i) e) where
  __ := he.option _ he.isIdempotentElem_sum.one_sub
    (by simp [sub_mul, he.isIdempotentElem_sum.eq]) (by simp [mul_sub, he.isIdempotentElem_sum.eq])
  complete := by
    rw [Fintype.sum_option]
    exact sub_add_cancel _ _

/--
lemma `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker_aux` / 引理 `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker_aux`

English:
lemma CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker_aux
  proof: by
  cases subsingleton_or_nontrivial R
  · choose e' he' using he'
    exact ⟨e', .of_subsingleton, funext he'⟩
  cases subsingleton_or_nontrivial S
  · obtain ⟨n, hn⟩ := h 1 (Subsingleton.elim _ _)
    simp at hn
  rcases n with - | n
  · simpa using he.complete
  obtain ⟨e', h₁, h₂⟩ := OrthogonalIdempotents.lift_of_isNilpotent_ker f h he.1 he'
  refine ⟨_, (equiv (finSuccEquiv n)).mpr
    (CompleteOrthogonalIdempotents.option (h₁.embedding (Fin.succEmb _))), funext fun i => ?_⟩
  have (i : _) : f (e' i) = e i := congr_fun h₂ i
  cases i using Fin.cases with
  | zero => simp [this, Fin.sum_univ_succ, ← he.complete]
  | succ i => simp [this]

中文:
引理 余mpleteOrthogonalIdempotents.lift_of_isNilpotent_ker_aux
  证明: by
  cases subsingleton_or_nontrivial R
  · choose e' he' using he'
    exact ⟨e', .of_subsingleton, funext he'⟩
  cases subsingleton_or_nontrivial S
  · obtain ⟨n, hn⟩ := h 1 (Subsingleton.elim _ _)
    simp at hn
  rcases n with - | n
  · simpa using he.complete
  obtain ⟨e', h₁, h₂⟩ := OrthogonalIdempotents.lift_of_isNilpotent_ker f h he.1 he'
  refine ⟨_, (equiv (finSuccEquiv n)).mpr
    (CompleteOrthogonalIdempotents.option (h₁.embedding (Fin.succEmb _))), funext fun i => ?_⟩
  have (i : _) : f (e' i) = e i := congr_fun h₂ i
  cases i using Fin.cases with
  | zero => simp [this, Fin.sum_univ_succ, ← he.complete]
  | succ i => simp [this]

Depends on / 依赖: CompleteOrthogonalIdempotents, CompleteOrthogonalIdempotents.option, Fin.succEmb, OrthogonalIdempotents, OrthogonalIdempotents.lift_of_isNilpotent_ker, Subsingleton, Subsingleton.elim, complete, congr_fun, embedding, finSuccEquiv, he.complete, lift_of_isNilpotent_ker, of_subsingleton, option, subsingleton_or_nontrivial, succEmb
-/
lemma CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker_aux
    (h : forall x in RingHom.ker f, IsNilpotent x)
    {n} {e : Fin n -> S} (he : CompleteOrthogonalIdempotents e) (he' : forall i, e i in f.range) :
    exists e' : Fin n -> R, CompleteOrthogonalIdempotents e' ∧ f ∘ e' = e := by
  cases subsingleton_or_nontrivial R
  · choose e' he' using he'
    exact ⟨e', .of_subsingleton, funext he'⟩
  cases subsingleton_or_nontrivial S
  · obtain ⟨n, hn⟩ := h 1 (Subsingleton.elim _ _)
    simp at hn
  rcases n with - | n
  · simpa using he.complete
  obtain ⟨e', h₁, h₂⟩ := OrthogonalIdempotents.lift_of_isNilpotent_ker f h he.1 he'
  refine ⟨_, (equiv (finSuccEquiv n)).mpr
    (CompleteOrthogonalIdempotents.option (h₁.embedding (Fin.succEmb _))), funext fun i => ?_⟩
  have (i : _) : f (e' i) = e i := congr_fun h₂ i
  cases i using Fin.cases with
  | zero => simp [this, Fin.sum_univ_succ, ← he.complete]
  | succ i => simp [this]

/--
lemma `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker` / 引理 `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`

English:
lemma CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
  proof: by
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker_aux f h
    ((equiv (Fintype.equivFin I).symm).mpr he) (fun _ => he' _)
  refine ⟨_, ((equiv (Fintype.equivFin I)).mpr h₁),
    by ext x; simpa using congr_fun h₂ (Fintype.equivFin I x)⟩

中文:
引理 余mpleteOrthogonalIdempotents.lift_of_isNilpotent_ker
  证明: by
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker_aux f h
    ((equiv (Fintype.equivFin I).symm).mpr he) (fun _ => he' _)
  refine ⟨_, ((equiv (Fintype.equivFin I)).mpr h₁),
    by ext x; simpa using congr_fun h₂ (Fintype.equivFin I x)⟩

Depends on / 依赖: Fintype, Fintype.equivFin, congr_fun, equivFin, lift_of_isNilpotent_ker_aux
-/
lemma CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
    (h : forall x in RingHom.ker f, IsNilpotent x)
    {e : I -> S} (he : CompleteOrthogonalIdempotents e) (he' : forall i, e i in f.range) :
    exists e' : I -> R, CompleteOrthogonalIdempotents e' ∧ f ∘ e' = e := by
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker_aux f h
    ((equiv (Fintype.equivFin I).symm).mpr he) (fun _ => he' _)
  refine ⟨_, ((equiv (Fintype.equivFin I)).mpr h₁),
    by ext x; simpa using congr_fun h₂ (Fintype.equivFin I x)⟩

/--
theorem `eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute` / 定理 `eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute`

English:
theorem eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute
  statement: {e₁ e₂ : R}
  proof: by
  have : (e₁ - e₂) ^ 3 = (e₁ - e₂) := by
    simp only [pow_succ, pow_zero, mul_sub, one_mul, sub_mul, he₁.eq, he₂.eq,
      H'.eq, mul_assoc]
    simp only [← mul_assoc, he₂.eq]
    abel
  obtain ⟨n, hn⟩ := H
  have : (e₁ - e₂) ^ (2 * n + 1) = (e₁ - e₂) := by
    clear hn; induction n <;> simp [mul_add, add_assoc, pow_add _ (2 * _) 3, ← pow_succ, *]
  rwa [pow_succ, two_mul, pow_add, hn, zero_mul, zero_mul, eq_comm, sub_eq_zero] at this

中文:
定理 eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute
  结论: {e₁ e₂ : R}
  证明: by
  have : (e₁ - e₂) ^ 3 = (e₁ - e₂) := by
    simp only [pow_succ, pow_zero, mul_sub, one_mul, sub_mul, he₁.eq, he₂.eq,
      H'.eq, mul_assoc]
    simp only [← mul_assoc, he₂.eq]
    abel
  obtain ⟨n, hn⟩ := H
  have : (e₁ - e₂) ^ (2 * n + 1) = (e₁ - e₂) := by
    clear hn; induction n <;> simp [mul_add, add_assoc, pow_add _ (2 * _) 3, ← pow_succ, *]
  rwa [pow_succ, two_mul, pow_add, hn, zero_mul, zero_mul, eq_comm, sub_eq_zero] at this

Depends on / 依赖: add_assoc, eq_comm, mul_add, mul_assoc, mul_sub, one_mul, pow_add, pow_succ, pow_zero, sub_eq_zero, sub_mul, two_mul, zero_mul
-/
theorem eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute {e₁ e₂ : R}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) (H : IsNilpotent (e₁ - e₂))
    (H' : Commute e₁ e₂) :
    e₁ = e₂ := by
  have : (e₁ - e₂) ^ 3 = (e₁ - e₂) := by
    simp only [pow_succ, pow_zero, mul_sub, one_mul, sub_mul, he₁.eq, he₂.eq,
      H'.eq, mul_assoc]
    simp only [← mul_assoc, he₂.eq]
    abel
  obtain ⟨n, hn⟩ := H
  have : (e₁ - e₂) ^ (2 * n + 1) = (e₁ - e₂) := by
    clear hn; induction n <;> simp [mul_add, add_assoc, pow_add _ (2 * _) 3, ← pow_succ, *]
  rwa [pow_succ, two_mul, pow_add, hn, zero_mul, zero_mul, eq_comm, sub_eq_zero] at this

/--
theorem `CompleteOrthogonalIdempotents.of_ker_isNilpotent_of_isMulCentral` / 定理 `CompleteOrthogonalIdempotents.of_ker_isNilpotent_of_isMulCentral`

English:
theorem CompleteOrthogonalIdempotents.of_ker_isNilpotent_of_isMulCentral
  proof: by
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker f h he'' (fun _ => ⟨_, rfl⟩)
  obtain rfl : e = e' := by
    ext i
    refine eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute
      (he _) (h₁.idem _) (h _ ?_) ((he' i).comm _)
    simpa [RingHom.mem_ker, sub_eq_zero] using congr_fun h₂.symm i
  exact h₁

中文:
定理 余mpleteOrthogonalIdempotents.of_ker_isNilpotent_of_isMulCentral
  证明: by
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker f h he'' (fun _ => ⟨_, rfl⟩)
  obtain rfl : e = e' := by
    ext i
    refine eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute
      (he _) (h₁.idem _) (h _ ?_) ((he' i).comm _)
    simpa [RingHom.mem_ker, sub_eq_zero] using congr_fun h₂.symm i
  exact h₁

Depends on / 依赖: RingHom, RingHom.mem_ker, congr_fun, eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute, lift_of_isNilpotent_ker, mem_ker, sub_eq_zero
-/
theorem CompleteOrthogonalIdempotents.of_ker_isNilpotent_of_isMulCentral
    (h : forall x in RingHom.ker f, IsNilpotent x)
    (he : forall i, IsIdempotentElem (e i))
    (he' : forall i, IsMulCentral (e i))
    (he'' : CompleteOrthogonalIdempotents (f ∘ e)) :
    CompleteOrthogonalIdempotents e := by
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker f h he'' (fun _ => ⟨_, rfl⟩)
  obtain rfl : e = e' := by
    ext i
    refine eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute
      (he _) (h₁.idem _) (h _ ?_) ((he' i).comm _)
    simpa [RingHom.mem_ker, sub_eq_zero] using congr_fun h₂.symm i
  exact h₁

end Ring

section CommRing

variable {R S : Type*} [CommRing R] [Ring S] (f : R ->+* S)

/--
theorem `eq_of_isNilpotent_sub_of_isIdempotentElem` / 定理 `eq_of_isNilpotent_sub_of_isIdempotentElem`

English:
theorem eq_of_isNilpotent_sub_of_isIdempotentElem
  statement: {e₁ e₂ : R}
  proof: eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute he₁ he₂ H (.all _ _)

@[stacks 00J9]

中文:
定理 eq_of_isNilpotent_sub_of_isIdempotentElem
  结论: {e₁ e₂ : R}
  证明: eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute he₁ he₂ H (.all _ _)

@[stacks 00J9]

Depends on / 依赖: eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute
-/
theorem eq_of_isNilpotent_sub_of_isIdempotentElem {e₁ e₂ : R}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) (H : IsNilpotent (e₁ - e₂)) :
    e₁ = e₂ :=
  eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute he₁ he₂ H (.all _ _)

@[stacks 00J9]
/--
theorem `existsUnique_isIdempotentElem_eq_of_ker_isNilpotent` / 定理 `existsUnique_isIdempotentElem_eq_of_ker_isNilpotent`

English:
theorem existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
  statement: (h : forall x in RingHom.ker f, IsNilpotent x)
  proof: by
  obtain ⟨e', he₂, rfl⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent f h e he he'
  exact ⟨e', ⟨he₂, rfl⟩, fun x ⟨hx, hx'⟩ =>
    eq_of_isNilpotent_sub_of_isIdempotentElem hx he₂
      (h _ (by rw [RingHom.mem_ker, map_sub, hx', sub_self]))⟩

中文:
定理 存在Unique_isIdempotentElem_eq_of_ker_isNilpotent
  结论: (h : 对任意 x in 环态射.ker f, 是幂零 x)
  证明: by
  obtain ⟨e', he₂, rfl⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent f h e he he'
  exact ⟨e', ⟨he₂, rfl⟩, fun x ⟨hx, hx'⟩ =>
    eq_of_isNilpotent_sub_of_isIdempotentElem hx he₂
      (h _ (by rw [RingHom.mem_ker, map_sub, hx', sub_self]))⟩

Depends on / 依赖: RingHom, RingHom.mem_ker, eq_of_isNilpotent_sub_of_isIdempotentElem, exists_isIdempotentElem_eq_of_ker_isNilpotent, map_sub, mem_ker, sub_self
-/
theorem existsUnique_isIdempotentElem_eq_of_ker_isNilpotent (h : forall x in RingHom.ker f, IsNilpotent x)
    (e : S) (he : e in f.range) (he' : IsIdempotentElem e) :
    exists! e' : R, IsIdempotentElem e' ∧ f e' = e := by
  obtain ⟨e', he₂, rfl⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent f h e he he'
  exact ⟨e', ⟨he₂, rfl⟩, fun x ⟨hx, hx'⟩ =>
    eq_of_isNilpotent_sub_of_isIdempotentElem hx he₂
      (h _ (by rw [RingHom.mem_ker, map_sub, hx', sub_self]))⟩

/--
lemma `OrthogonalIdempotents.surjective_pi` / 引理 `OrthogonalIdempotents.surjective_pi`

English:
lemma OrthogonalIdempotents.surjective_pi
  statement: {I : Type*} [Finite I] {e : I -> R}
  proof: by
  suffices Pairwise fun i j => IsCoprime (Ideal.span {1 - e i}) (Ideal.span {1 - e j}) by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.quotientInfToPiQuotient_surj this x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨x, by ext i; simp [Ideal.quotientInfToPiQuotient]⟩
  intro i j hij
  rw [Ideal.isCoprime_span_singleton_iff]
  exact ⟨1, e i, by simp [mul_sub, he.ortho hij]⟩

中文:
引理 正交幂等.surjective_pi
  结论: {I : 类型} [有限 I] {e : I -> R}
  证明: by
  suffices Pairwise fun i j => IsCoprime (Ideal.span {1 - e i}) (Ideal.span {1 - e j}) by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.quotientInfToPiQuotient_surj this x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨x, by ext i; simp [Ideal.quotientInfToPiQuotient]⟩
  intro i j hij
  rw [Ideal.isCoprime_span_singleton_iff]
  exact ⟨1, e i, by simp [mul_sub, he.ortho hij]⟩

Depends on / 依赖: Ideal.Quotient.mk_surjective, Ideal.isCoprime_span_singleton_iff, Ideal.quotientInfToPiQuotient, Ideal.quotientInfToPiQuotient_surj, Ideal.span, IsCoprime, Pairwise, Quotient, he.ortho, isCoprime_span_singleton_iff, mk_surjective, mul_sub, quotientInfToPiQuotient, quotientInfToPiQuotient_surj
-/
lemma OrthogonalIdempotents.surjective_pi {I : Type*} [Finite I] {e : I -> R}
    (he : OrthogonalIdempotents e) :
    Function.Surjective (RingHom.pi fun i => Ideal.Quotient.mk (Ideal.span {1 - e i})) := by
  suffices Pairwise fun i j => IsCoprime (Ideal.span {1 - e i}) (Ideal.span {1 - e j}) by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.quotientInfToPiQuotient_surj this x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨x, by ext i; simp [Ideal.quotientInfToPiQuotient]⟩
  intro i j hij
  rw [Ideal.isCoprime_span_singleton_iff]
  exact ⟨1, e i, by simp [mul_sub, he.ortho hij]⟩

/--
lemma `OrthogonalIdempotents.prod_one_sub` / 引理 `OrthogonalIdempotents.prod_one_sub`

English:
lemma OrthogonalIdempotents.prod_one_sub
  statement: {I : Type*} {e : I -> R}
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp [ih, sub_mul, mul_sub, he.mul_sum_of_notMem has, sub_sub]

中文:
引理 正交幂等.prod_one_sub
  结论: {I : 类型} {e : I -> R}
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp [ih, sub_mul, mul_sub, he.mul_sum_of_notMem has, sub_sub]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction, he.mul_sum_of_notMem, mul_sub, mul_sum_of_notMem, sub_mul, sub_sub
-/
lemma OrthogonalIdempotents.prod_one_sub {I : Type*} {e : I -> R}
    (he : OrthogonalIdempotents e) (s : Finset I) :
    ∏ i in s, (1 - e i) = 1 - ∑ i in s, e i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp [ih, sub_mul, mul_sub, he.mul_sum_of_notMem has, sub_sub]

variable {I : Type*} [Fintype I] {e : I -> R}

/--
theorem `CompleteOrthogonalIdempotents.of_ker_isNilpotent` / 定理 `CompleteOrthogonalIdempotents.of_ker_isNilpotent`

English:
theorem CompleteOrthogonalIdempotents.of_ker_isNilpotent
  statement: (h : forall x in RingHom.ker f, IsNilpotent x)
  proof: of_ker_isNilpotent_of_isMulCentral f h he
    (fun _ => Semigroup.mem_center_iff.mpr (mul_comm · _)) he'

中文:
定理 余mpleteOrthogonalIdempotents.of_ker_isNilpotent
  结论: (h : 对任意 x in 环态射.ker f, 是幂零 x)
  证明: of_ker_isNilpotent_of_isMulCentral f h he
    (fun _ => Semigroup.mem_center_iff.mpr (mul_comm · _)) he'

Depends on / 依赖: Semigroup, Semigroup.mem_center_iff.mpr, mem_center_iff, mul_comm, of_ker_isNilpotent_of_isMulCentral
-/
theorem CompleteOrthogonalIdempotents.of_ker_isNilpotent (h : forall x in RingHom.ker f, IsNilpotent x)
    (he : forall i, IsIdempotentElem (e i))
    (he' : CompleteOrthogonalIdempotents (f ∘ e)) :
    CompleteOrthogonalIdempotents e :=
  of_ker_isNilpotent_of_isMulCentral f h he
    (fun _ => Semigroup.mem_center_iff.mpr (mul_comm · _)) he'

/--
lemma `CompleteOrthogonalIdempotents.prod_one_sub` / 引理 `CompleteOrthogonalIdempotents.prod_one_sub`

English:
lemma CompleteOrthogonalIdempotents.prod_one_sub
  proof: by
  rw [he.1.prod_one_sub]; rw [he.complete]; rw [sub_self]

中文:
引理 余mpleteOrthogonalIdempotents.prod_one_sub
  证明: by
  rw [he.1.prod_one_sub]; rw [he.complete]; rw [sub_self]

Depends on / 依赖: complete, he.complete, prod_one_sub, sub_self
-/
lemma CompleteOrthogonalIdempotents.prod_one_sub
    (he : CompleteOrthogonalIdempotents e) :
    ∏ i, (1 - e i) = 0 := by
  rw [he.1.prod_one_sub]; rw [he.complete]; rw [sub_self]

/--
lemma `CompleteOrthogonalIdempotents.of_prod_one_sub` / 引理 `CompleteOrthogonalIdempotents.of_prod_one_sub`

English:
lemma CompleteOrthogonalIdempotents.of_prod_one_sub
  proof: he
  complete := by rwa [he.prod_one_sub, sub_eq_zero, eq_comm] at he'

中文:
引理 余mpleteOrthogonalIdempotents.of_prod_one_sub
  证明: he
  complete := by rwa [he.prod_one_sub, sub_eq_zero, eq_comm] at he'
-/
lemma CompleteOrthogonalIdempotents.of_prod_one_sub
    (he : OrthogonalIdempotents e) (he' : ∏ i, (1 - e i) = 0) :
    CompleteOrthogonalIdempotents e where
  __ := he
  complete := by rwa [he.prod_one_sub, sub_eq_zero, eq_comm] at he'

/--
lemma `CompleteOrthogonalIdempotents.bijective_pi` / 引理 `CompleteOrthogonalIdempotents.bijective_pi`

English:
lemma CompleteOrthogonalIdempotents.bijective_pi
  given: (he : CompleteOrthogonalIdempotents e)
  proof: by
  classical
  refine ⟨?_, he.1.surjective_pi⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  simp only [funext_iff, RingHom.pi_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hx
  suffices forall s : Finset I, (∏ i in s, (1 - e i)) * x = x by
    rw [← this Finset.univ]; rw [he.prod_one_sub]; rw [zero_mul]
  refine fun s => Finset.induction_on s (by simp) ?_
  intro a s has e'
  suffices (1 - e a) * x = x by simp [has, mul_assoc, e', this]
  obtain ⟨c, rfl⟩ := hx a
  rw [← mul_assoc]; rw [(he.idem a).one_sub.eq]

中文:
引理 余mpleteOrthogonalIdempotents.bijective_pi
  条件: (he : 余mpleteOrthogonalIdempotents e)
  证明: by
  classical
  refine ⟨?_, he.1.surjective_pi⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  simp only [funext_iff, RingHom.pi_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hx
  suffices forall s : Finset I, (∏ i in s, (1 - e i)) * x = x by
    rw [← this Finset.univ]; rw [he.prod_one_sub]; rw [zero_mul]
  refine fun s => Finset.induction_on s (by simp) ?_
  intro a s has e'
  suffices (1 - e a) * x = x by simp [has, mul_assoc, e', this]
  obtain ⟨c, rfl⟩ := hx a
  rw [← mul_assoc]; rw [(he.idem a).one_sub.eq]

Depends on / 依赖: Finset, Finset.induction_on, Finset.univ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Pi.zero_apply, Quotient, RingHom, RingHom.pi_apply, classical, eq_zero_iff_mem, funext_iff, he.prod_one_sub, induction_on, injective_iff_map_eq_zero, mem_span_singleton, mul_assoc, pi_apply, prod_one_sub, surjective_pi
-/
lemma CompleteOrthogonalIdempotents.bijective_pi (he : CompleteOrthogonalIdempotents e) :
    Function.Bijective (RingHom.pi fun i => Ideal.Quotient.mk (Ideal.span {1 - e i})) := by
  classical
  refine ⟨?_, he.1.surjective_pi⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  simp only [funext_iff, RingHom.pi_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hx
  suffices forall s : Finset I, (∏ i in s, (1 - e i)) * x = x by
    rw [← this Finset.univ]; rw [he.prod_one_sub]; rw [zero_mul]
  refine fun s => Finset.induction_on s (by simp) ?_
  intro a s has e'
  suffices (1 - e a) * x = x by simp [has, mul_assoc, e', this]
  obtain ⟨c, rfl⟩ := hx a
  rw [← mul_assoc]; rw [(he.idem a).one_sub.eq]

/--
lemma `CompleteOrthogonalIdempotents.bijective_pi'` / 引理 `CompleteOrthogonalIdempotents.bijective_pi'`

English:
lemma CompleteOrthogonalIdempotents.bijective_pi'
  given: (he : CompleteOrthogonalIdempotents (1 - e ·))
  proof: by
  obtain ⟨e', rfl, h⟩ : exists e' : I -> R, (e' = e) ∧ Function.Bijective (RingHom.pi fun i =>
      Ideal.Quotient.mk (Ideal.span {e' i})) := ⟨_, funext (by simp), he.bijective_pi⟩
  exact h

中文:
引理 余mpleteOrthogonalIdempotents.bijective_pi'
  条件: (he : 余mpleteOrthogonalIdempotents (1 - e ·))
  证明: by
  obtain ⟨e', rfl, h⟩ : exists e' : I -> R, (e' = e) ∧ Function.Bijective (RingHom.pi fun i =>
      Ideal.Quotient.mk (Ideal.span {e' i})) := ⟨_, funext (by simp), he.bijective_pi⟩
  exact h

Depends on / 依赖: Bijective, Function, Function.Bijective, Ideal.Quotient.mk, Ideal.span, Quotient, RingHom, RingHom.pi, bijective_pi, he.bijective_pi
-/
lemma CompleteOrthogonalIdempotents.bijective_pi' (he : CompleteOrthogonalIdempotents (1 - e ·)) :
    Function.Bijective (RingHom.pi fun i => Ideal.Quotient.mk (Ideal.span {e i})) := by
  obtain ⟨e', rfl, h⟩ : exists e' : I -> R, (e' = e) ∧ Function.Bijective (RingHom.pi fun i =>
      Ideal.Quotient.mk (Ideal.span {e' i})) := ⟨_, funext (by simp), he.bijective_pi⟩
  exact h

/--
lemma `RingHom.pi_bijective_of_isIdempotentElem` / 引理 `RingHom.pi_bijective_of_isIdempotentElem`

English:
lemma RingHom.pi_bijective_of_isIdempotentElem
  statement: (e : I -> R)
  proof: (CompleteOrthogonalIdempotents.of_prod_one_sub
      ⟨fun i => (he i).one_sub, he₁⟩ (by simpa using he₂)).bijective_pi'

中文:
引理 环态射.pi_bijective_of_isIdempotentElem
  结论: (e : I -> R)
  证明: (CompleteOrthogonalIdempotents.of_prod_one_sub
      ⟨fun i => (he i).one_sub, he₁⟩ (by simpa using he₂)).bijective_pi'

Depends on / 依赖: CompleteOrthogonalIdempotents, CompleteOrthogonalIdempotents.of_prod_one_sub, bijective_pi, of_prod_one_sub, one_sub
-/
lemma RingHom.pi_bijective_of_isIdempotentElem (e : I -> R)
    (he : forall i, IsIdempotentElem (e i))
    (he₁ : forall i j, i != j -> (1 - e i) * (1 - e j) = 0) (he₂ : ∏ i, e i = 0) :
    Function.Bijective (RingHom.pi fun i => Ideal.Quotient.mk (Ideal.span {e i})) :=
  (CompleteOrthogonalIdempotents.of_prod_one_sub
      ⟨fun i => (he i).one_sub, he₁⟩ (by simpa using he₂)).bijective_pi'

/--
lemma `RingHom.prod_bijective_of_isIdempotentElem` / 引理 `RingHom.prod_bijective_of_isIdempotentElem`

English:
lemma RingHom.prod_bijective_of_isIdempotentElem
  statement: {e f : R} (he : IsIdempotentElem e)
  proof: by
  let o (i : Fin 2) : R := match i with
    | 0 => e
    | 1 => f
  change Function.Bijective
    (piFinTwoEquiv _ ∘ RingHom.pi (fun i : Fin 2 => Ideal.Quotient.mk (Ideal.span {o i})))
  rw [(Equiv.bijective _).of_comp_iff']
  apply pi_bijective_of_isIdempotentElem
  · intro i
    fin_cases i <;> simpa [o]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      simp [o, mul_comm, hef₂, ← hef₁]
  · simpa

中文:
引理 环态射.prod_bijective_of_isIdempotentElem
  结论: {e f : R} (he : IsIdempotentElem e)
  证明: by
  let o (i : Fin 2) : R := match i with
    | 0 => e
    | 1 => f
  change Function.Bijective
    (piFinTwoEquiv _ ∘ RingHom.pi (fun i : Fin 2 => Ideal.Quotient.mk (Ideal.span {o i})))
  rw [(Equiv.bijective _).of_comp_iff']
  apply pi_bijective_of_isIdempotentElem
  · intro i
    fin_cases i <;> simpa [o]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      simp [o, mul_comm, hef₂, ← hef₁]
  · simpa

Depends on / 依赖: Bijective, Equiv.bijective, Function, Function.Bijective, Ideal.Quotient.mk, Ideal.span, Quotient, RingHom, RingHom.pi, bijective, fin_cases, mul_comm, of_comp_iff, piFinTwoEquiv, pi_bijective_of_isIdempotentElem
-/
lemma RingHom.prod_bijective_of_isIdempotentElem {e f : R} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (hef₁ : e + f = 1) (hef₂ : e * f = 0) :
    Function.Bijective ((Ideal.Quotient.mk <| Ideal.span {e}).prod
      (Ideal.Quotient.mk <| Ideal.span {f})) := by
  let o (i : Fin 2) : R := match i with
    | 0 => e
    | 1 => f
  change Function.Bijective
    (piFinTwoEquiv _ ∘ RingHom.pi (fun i : Fin 2 => Ideal.Quotient.mk (Ideal.span {o i})))
  rw [(Equiv.bijective _).of_comp_iff']
  apply pi_bijective_of_isIdempotentElem
  · intro i
    fin_cases i <;> simpa [o]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      simp [o, mul_comm, hef₂, ← hef₁]
  · simpa

variable (R) in
/-- If `e` and `f` are idempotent elements such that `e + f = 1` and `e * f = 0`,
`S` is isomorphic as an `R`-algebra to `S ⧸ (e) × S ⧸ (f)`. -/
@[simps! -isSimp apply, simps! apply_fst apply_snd]
/--
Definition of `AlgEquiv.prodQuotientOfIsIdempotentElem` / `AlgEquiv.prodQuotientOfIsIdempotentElem` 的定义

English:
definition AlgEquiv.prodQuotientOfIsIdempotentElem
  body: AlgEquiv.ofBijective ((Ideal.Quotient.mkₐ _ _).prod (Ideal.Quotient.mkₐ _ _))
    RingHom.prod_bijective_of_isIdempotentElem he hf hef₁ hef₂

中文:
定义 代数等价.prodQuotientOfIsIdempotentElem
  定义体: AlgEquiv.ofBijective ((Ideal.Quotient.mkₐ _ _).prod (Ideal.Quotient.mkₐ _ _))
    RingHom.prod_bijective_of_isIdempotentElem he hf hef₁ hef₂

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, Ideal.Quotient.mk, Quotient, RingHom, RingHom.prod_bijective_of_isIdempotentElem, ofBijective, prod_bijective_of_isIdempotentElem
-/
noncomputable def AlgEquiv.prodQuotientOfIsIdempotentElem
    {S : Type*} [CommRing S] [Algebra R S] {e f : S} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (hef₁ : e + f = 1) (hef₂ : e * f = 0) :
    S ≃ₐ[R] (S ⧸ Ideal.span {e}) × S ⧸ Ideal.span {f} :=
AlgEquiv.ofBijective ((Ideal.Quotient.mkₐ _ _).prod (Ideal.Quotient.mkₐ _ _))
    RingHom.prod_bijective_of_isIdempotentElem he hf hef₁ hef₂

/--
lemma `CompleteOrthogonalIdempotents.exists_eq_comp_of_ker_eq_span` / 引理 `CompleteOrthogonalIdempotents.exists_eq_comp_of_ker_eq_span`

English:
lemma CompleteOrthogonalIdempotents.exists_eq_comp_of_ker_eq_span
  proof: by
  choose e' he' using hef
  choose k hk using fun i => Ideal.mem_span_singleton.mp
      (hfe₀.le (show f (e' i * e' i - e' i) = 0 by simp [he', (he.1.1 i).eq]))
  refine ⟨(1 - e₀) • e', ⟨⟨Option.rec he₀ fun i => ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro (_|i) (_|j) h
    · simp at h
    · dsimp; linear_combination - he₀.eq * e' j
    · dsimp; linear_combination - he₀.eq * e' i
    · obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp
        (hfe₀.le (show f (e' i * e' j) = 0 by simp [he', he.1.2 (by simpa using h)]))
      dsimp
      rw [mul_mul_mul_comm]; rw [hk]; rw [he₀.one_sub.eq]; rw [← mul_assoc]; rw [he₀.one_sub_mul_self]; rw [zero_mul]
  · obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp
      (hfe₀.le (show f (∑ i, e' i - 1) = 0 by simpa [he', sub_eq_zero] using he.2))
    simp only [Fintype.sum_option, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      sub_eq_iff_eq_add.mp hk]
    linear_combination - he₀.eq * k
  · have : f e₀ = 0 := by simpa using hfe₀.ge (Ideal.mem_span_singleton_self _)
    aesop
  · dsimp [IsIdempotentElem]
    linear_combination congr($(he₀.eq) * ((e' i) ^ 2 - k i) + (1 - e₀) * $(hk i))

中文:
引理 余mpleteOrthogonalIdempotents.存在_eq_comp_of_ker_eq_span
  证明: by
  choose e' he' using hef
  choose k hk using fun i => Ideal.mem_span_singleton.mp
      (hfe₀.le (show f (e' i * e' i - e' i) = 0 by simp [he', (he.1.1 i).eq]))
  refine ⟨(1 - e₀) • e', ⟨⟨Option.rec he₀ fun i => ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro (_|i) (_|j) h
    · simp at h
    · dsimp; linear_combination - he₀.eq * e' j
    · dsimp; linear_combination - he₀.eq * e' i
    · obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp
        (hfe₀.le (show f (e' i * e' j) = 0 by simp [he', he.1.2 (by simpa using h)]))
      dsimp
      rw [mul_mul_mul_comm]; rw [hk]; rw [he₀.one_sub.eq]; rw [← mul_assoc]; rw [he₀.one_sub_mul_self]; rw [zero_mul]
  · obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp
      (hfe₀.le (show f (∑ i, e' i - 1) = 0 by simpa [he', sub_eq_zero] using he.2))
    simp only [Fintype.sum_option, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      sub_eq_iff_eq_add.mp hk]
    linear_combination - he₀.eq * k
  · have : f e₀ = 0 := by simpa using hfe₀.ge (Ideal.mem_span_singleton_self _)
    aesop
  · dsimp [IsIdempotentElem]
    linear_combination congr($(he₀.eq) * ((e' i) ^ 2 - k i) + (1 - e₀) * $(hk i))

Depends on / 依赖: Ideal.mem_span_singleton.mp, Option.rec, linear_combination, mem_span_singleton, mul_mul_mul_comm
-/
lemma CompleteOrthogonalIdempotents.exists_eq_comp_of_ker_eq_span
    (f : R ->+* S) (e₀ : R) (he₀ : IsIdempotentElem e₀) (hfe₀ : RingHom.ker f = .span {e₀})
    (e : I -> S) (he : CompleteOrthogonalIdempotents e) (hef : forall i, e i in f.range) :
    exists e', CompleteOrthogonalIdempotents (Option.rec e₀ e') ∧ e = f ∘ e' := by
  choose e' he' using hef
  choose k hk using fun i => Ideal.mem_span_singleton.mp
      (hfe₀.le (show f (e' i * e' i - e' i) = 0 by simp [he', (he.1.1 i).eq]))
  refine ⟨(1 - e₀) • e', ⟨⟨Option.rec he₀ fun i => ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro (_|i) (_|j) h
    · simp at h
    · dsimp; linear_combination - he₀.eq * e' j
    · dsimp; linear_combination - he₀.eq * e' i
    · obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp
        (hfe₀.le (show f (e' i * e' j) = 0 by simp [he', he.1.2 (by simpa using h)]))
      dsimp
      rw [mul_mul_mul_comm]; rw [hk]; rw [he₀.one_sub.eq]; rw [← mul_assoc]; rw [he₀.one_sub_mul_self]; rw [zero_mul]
  · obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp
      (hfe₀.le (show f (∑ i, e' i - 1) = 0 by simpa [he', sub_eq_zero] using he.2))
    simp only [Fintype.sum_option, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      sub_eq_iff_eq_add.mp hk]
    linear_combination - he₀.eq * k
  · have : f e₀ = 0 := by simpa using hfe₀.ge (Ideal.mem_span_singleton_self _)
    aesop
  · dsimp [IsIdempotentElem]
    linear_combination congr($(he₀.eq) * ((e' i) ^ 2 - k i) + (1 - e₀) * $(hk i))

end CommRing

section corner

variable {R : Type*} (e : R)

namespace Subsemigroup

variable [Semigroup R]

/--
Definition of `corner` / `corner` 的定义

English:
definition corner
  signature: : Subsemigroup R where
  body: Set.range (e * · * e)
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * e * e * b, by simp_rw [mul_assoc]⟩

中文:
定义 corner
  签名: : 子半群 R where
  定义体: Set.range (e * · * e)
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * e * e * b, by simp_rw [mul_assoc]⟩

Depends on / 依赖: Set.range
-/
def corner : Subsemigroup R where
  carrier := Set.range (e * · * e)
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * e * e * b, by simp_rw [mul_assoc]⟩

variable {e} (idem : IsIdempotentElem e)
include idem

/--
lemma `mem_corner_iff` / 引理 `mem_corner_iff`

English:
lemma mem_corner_iff
  given: {r : R}
  statement: r in corner e ↔ e * r = r ∧ r * e = r
  proof: ⟨by rintro ⟨r, rfl⟩; simp_rw [← mul_assoc, idem.eq, mul_assoc, idem.eq, true_and],
    (⟨r, by simp_rw [·]⟩)⟩

中文:
引理 mem_corner_iff
  条件: {r : R}
  结论: r in corner e ↔ e * r = r ∧ r * e = r
  证明: ⟨by rintro ⟨r, rfl⟩; simp_rw [← mul_assoc, idem.eq, mul_assoc, idem.eq, true_and],
    (⟨r, by simp_rw [·]⟩)⟩

Depends on / 依赖: idem.eq, mul_assoc, simp_rw, true_and
-/
lemma mem_corner_iff {r : R} : r in corner e ↔ e * r = r ∧ r * e = r :=
  ⟨by rintro ⟨r, rfl⟩; simp_rw [← mul_assoc, idem.eq, mul_assoc, idem.eq, true_and],
    (⟨r, by simp_rw [·]⟩)⟩

/--
lemma `mem_corner_iff_mul_left` / 引理 `mem_corner_iff_mul_left`

English:
lemma mem_corner_iff_mul_left
  given: (hc : IsMulCentral e) {r : R}
  statement: r in corner e ↔ e * r = r
  proof: by
  rw [mem_corner_iff idem]; rw [and_iff_left_of_imp]; intro; rwa [← hc.comm]

中文:
引理 mem_corner_iff_mul_left
  条件: (hc : 是MulCentral e) {r : R}
  结论: r in corner e ↔ e * r = r
  证明: by
  rw [mem_corner_iff idem]; rw [and_iff_left_of_imp]; intro; rwa [← hc.comm]

Depends on / 依赖: and_iff_left_of_imp, hc.comm, mem_corner_iff
-/
lemma mem_corner_iff_mul_left (hc : IsMulCentral e) {r : R} : r in corner e ↔ e * r = r := by
  rw [mem_corner_iff idem]; rw [and_iff_left_of_imp]; intro; rwa [← hc.comm]

/--
lemma `mem_corner_iff_mul_right` / 引理 `mem_corner_iff_mul_right`

English:
lemma mem_corner_iff_mul_right
  given: (hc : IsMulCentral e) {r : R}
  statement: r in corner e ↔ r * e = r
  proof: by
  rw [mem_corner_iff_mul_left idem hc]; rw [hc.comm]

中文:
引理 mem_corner_iff_mul_right
  条件: (hc : 是MulCentral e) {r : R}
  结论: r in corner e ↔ r * e = r
  证明: by
  rw [mem_corner_iff_mul_left idem hc]; rw [hc.comm]

Depends on / 依赖: hc.comm, mem_corner_iff_mul_left
-/
lemma mem_corner_iff_mul_right (hc : IsMulCentral e) {r : R} : r in corner e ↔ r * e = r := by
  rw [mem_corner_iff_mul_left idem hc]; rw [hc.comm]

/--
lemma `mem_corner_iff_mem_range_mul_left` / 引理 `mem_corner_iff_mem_range_mul_left`

English:
lemma mem_corner_iff_mem_range_mul_left
  given: (hc : IsMulCentral e) {r : R}
  proof: by
  simp_rw [corner, mem_mk, Set.mem_range, ← (hc.comm _).eq, ← mul_assoc, idem.eq]

中文:
引理 mem_corner_iff_mem_range_mul_left
  条件: (hc : 是MulCentral e) {r : R}
  证明: by
  simp_rw [corner, mem_mk, Set.mem_range, ← (hc.comm _).eq, ← mul_assoc, idem.eq]

Depends on / 依赖: Set.mem_range, corner, hc.comm, idem.eq, mem_mk, mem_range, mul_assoc, simp_rw
-/
lemma mem_corner_iff_mem_range_mul_left (hc : IsMulCentral e) {r : R} :
    r in corner e ↔ r in Set.range (e * ·) := by
  simp_rw [corner, mem_mk, Set.mem_range, ← (hc.comm _).eq, ← mul_assoc, idem.eq]

/--
lemma `mem_corner_iff_mem_range_mul_right` / 引理 `mem_corner_iff_mem_range_mul_right`

English:
lemma mem_corner_iff_mem_range_mul_right
  given: (hc : IsMulCentral e) {r : R}
  proof: by
  simp_rw [mem_corner_iff_mem_range_mul_left idem hc, (hc.comm _).eq]

中文:
引理 mem_corner_iff_mem_range_mul_right
  条件: (hc : 是MulCentral e) {r : R}
  证明: by
  simp_rw [mem_corner_iff_mem_range_mul_left idem hc, (hc.comm _).eq]

Depends on / 依赖: hc.comm, mem_corner_iff_mem_range_mul_left, simp_rw
-/
lemma mem_corner_iff_mem_range_mul_right (hc : IsMulCentral e) {r : R} :
    r in corner e ↔ r in Set.range (· * e) := by
  simp_rw [mem_corner_iff_mem_range_mul_left idem hc, (hc.comm _).eq]

/-- The corner associated to an idempotent `e` in a semiring without 1
is the semiring with `e` as 1 consisting of all element of the form `e * r * e`. -/
@[nolint unusedArguments]
/--
Definition of `_root_.IsIdempotentElem.Corner` / `_root_.IsIdempotentElem.Corner` 的定义

English:
definition _root_.IsIdempotentElem.Corner
  signature: (_ : IsIdempotentElem e)
  body: Subsemigroup.corner e

中文:
定义 _root_.IsIdempotentElem.Corner
  签名: (_ : IsIdempotentElem e)
  定义体: Subsemigroup.corner e

Depends on / 依赖: Subsemigroup, Subsemigroup.corner, corner
-/
def _root_.IsIdempotentElem.Corner (_ : IsIdempotentElem e) : Type _ := Subsemigroup.corner e

end Subsemigroup

/--
Definition of `NonUnitalSubsemiring.corner` / `NonUnitalSubsemiring.corner` 的定义

English:
definition NonUnitalSubsemiring.corner
  signature: [NonUnitalSemiring R]
  body: Subsemigroup.corner e
  add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by simp_rw [mul_add, add_mul]⟩
  zero_mem' := ⟨0, by simp_rw [mul_zero, zero_mul]⟩

中文:
定义 NonUnital子半环.corner
  签名: [非幺半环 R]
  定义体: Subsemigroup.corner e
  add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by simp_rw [mul_add, add_mul]⟩
  zero_mem' := ⟨0, by simp_rw [mul_zero, zero_mul]⟩

Depends on / 依赖: DiscreteTopology, Finite, JacobsonSpace, Subsemigroup, Subsemigroup.corner, corner
-/
def NonUnitalSubsemiring.corner [NonUnitalSemiring R] : NonUnitalSubsemiring R where
  __ := Subsemigroup.corner e
  add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by simp_rw [mul_add, add_mul]⟩
  zero_mem' := ⟨0, by simp_rw [mul_zero, zero_mul]⟩

/--
Definition of `NonUnitalRing.corner` / `NonUnitalRing.corner` 的定义

English:
definition NonUnitalRing.corner
  signature: [NonUnitalRing R]
  body: NonUnitalSubsemiring.corner e
  neg_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, by simp_rw [mul_neg, neg_mul]⟩

中文:
定义 非幺环.corner
  签名: [非幺环 R]
  定义体: NonUnitalSubsemiring.corner e
  neg_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, by simp_rw [mul_neg, neg_mul]⟩

Depends on / 依赖: JacobsonSpace, NonUnitalSubsemiring, NonUnitalSubsemiring.corner, T1Space, corner
-/
def NonUnitalRing.corner [NonUnitalRing R] : NonUnitalSubring R where
  __ := NonUnitalSubsemiring.corner e
  neg_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, by simp_rw [mul_neg, neg_mul]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSemiring
  signature: R] (idem
  body: inferInstanceAs NonUnitalSemiring (NonUnitalSubsemiring.corner e)
  one := ⟨e, e, by simp_rw [idem.eq]⟩
  one_mul r := Subtype.ext ((Subsemigroup.mem_corner_iff idem).mp r.2).1
  mul_one r := Subtype.ext ((Subsemigroup.mem_corner_iff idem).mp r.2).2

中文:
实例 [非幺半环
  签名: R] (idem
  定义体: inferInstanceAs NonUnitalSemiring (NonUnitalSubsemiring.corner e)
  one := ⟨e, e, by simp_rw [idem.eq]⟩
  one_mul r := Subtype.ext ((Subsemigroup.mem_corner_iff idem).mp r.2).1
  mul_one r := Subtype.ext ((Subsemigroup.mem_corner_iff idem).mp r.2).2

Depends on / 依赖: NonUnitalSemiring, NonUnitalSubsemiring, NonUnitalSubsemiring.corner, Subsemigroup, Subsemigroup.mem_corner_iff, Subtype, Subtype.ext, corner, idem.eq, mem_corner_iff, mul_one, one_mul, simp_rw
-/
instance [NonUnitalSemiring R] (idem : IsIdempotentElem e) : Semiring idem.Corner where
  __ : NonUnitalSemiring idem.Corner :=
inferInstanceAs NonUnitalSemiring (NonUnitalSubsemiring.corner e)
  one := ⟨e, e, by simp_rw [idem.eq]⟩
  one_mul r := Subtype.ext ((Subsemigroup.mem_corner_iff idem).mp r.2).1
  mul_one r := Subtype.ext ((Subsemigroup.mem_corner_iff idem).mp r.2).2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommSemiring
  signature: R] (idem
  body: inferInstance
  __ : NonUnitalCommSemiring idem.Corner :=
inferInstanceAs NonUnitalCommSemiring (NonUnitalSubsemiring.corner e)

中文:
实例 [非幺交换半环
  签名: R] (idem
  定义体: inferInstance
  __ : NonUnitalCommSemiring idem.Corner :=
inferInstanceAs NonUnitalCommSemiring (NonUnitalSubsemiring.corner e)
-/
instance [NonUnitalCommSemiring R] (idem : IsIdempotentElem e) : CommSemiring idem.Corner where
  __ : Semiring idem.Corner := inferInstance
  __ : NonUnitalCommSemiring idem.Corner :=
inferInstanceAs NonUnitalCommSemiring (NonUnitalSubsemiring.corner e)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalRing
  signature: R] (idem
  body: inferInstance
__ : NonUnitalRing idem.Corner := inferInstanceAs NonUnitalRing (NonUnitalRing.corner e)

中文:
实例 [非幺环
  签名: R] (idem
  定义体: inferInstance
__ : NonUnitalRing idem.Corner := inferInstanceAs NonUnitalRing (NonUnitalRing.corner e)
-/
instance [NonUnitalRing R] (idem : IsIdempotentElem e) : Ring idem.Corner where
  __ : Semiring idem.Corner := inferInstance
__ : NonUnitalRing idem.Corner := inferInstanceAs NonUnitalRing (NonUnitalRing.corner e)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommRing
  signature: R] (idem
  body: inferInstance
  __ : NonUnitalCommRing idem.Corner :=
inferInstanceAs NonUnitalCommRing (NonUnitalRing.corner e)

中文:
实例 [非幺交换环
  签名: R] (idem
  定义体: inferInstance
  __ : NonUnitalCommRing idem.Corner :=
inferInstanceAs NonUnitalCommRing (NonUnitalRing.corner e)
-/
instance [NonUnitalCommRing R] (idem : IsIdempotentElem e) : CommRing idem.Corner where
  __ : Ring idem.Corner := inferInstance
  __ : NonUnitalCommRing idem.Corner :=
inferInstanceAs NonUnitalCommRing (NonUnitalRing.corner e)

variable {I : Type*} [Fintype I] {e : I -> R}

/--
Definition of `CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral` / `CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral` 的定义

English:
definition CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral
  signature: [Semiring R]
  body: ⟨_, r, rfl⟩
  invFun r := ∑ i, (r i).1
  left_inv r := by
    simp_rw [((hc _).comm _).eq, mul_assoc, (he.idem _).eq, ← Finset.mul_sum, he.complete, mul_one]
right_inv r := funext fun i => Subtype.ext by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_eq_single i _ (by simp at ·)]
    · have ⟨r', eq⟩ := (r i).2
      rw [← eq]; simp_rw [← mul_assoc, (he.idem i).eq, mul_assoc, (he.idem i).eq]
    · intro j _ ne; have ⟨r', eq⟩ := (r j).2
      rw [← eq]; simp_rw [← mul_assoc, he.ortho ne.symm, zero_mul]
map_mul' r₁ r₂ := funext fun i => Subtype.ext
    calc e i * (r₁ * r₂) * e i
     _ = e i * (r₁ * e i * r₂) * e i := by
       simp_rw [← ((hc i).comm r₁).eq, ← mul_assoc, (he.idem i).eq]
     _ = e i * r₁ * e i * (e i * r₂ * e i) := by
      conv in (r₁ * _ * r₂) => rw [← (he.idem i).eq]
      simp_rw [mul_assoc]
map_add' r₁ r₂ := funext fun i => Subtype.ext by simpa [mul_add] using! add_mul ..

中文:
定义 余mpleteOrthogonalIdempotents.ringEquivOfIsMulCentral
  签名: [半环 R]
  定义体: ⟨_, r, rfl⟩
  invFun r := ∑ i, (r i).1
  left_inv r := by
    simp_rw [((hc _).comm _).eq, mul_assoc, (he.idem _).eq, ← Finset.mul_sum, he.complete, mul_one]
right_inv r := funext fun i => Subtype.ext by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_eq_single i _ (by simp at ·)]
    · have ⟨r', eq⟩ := (r i).2
      rw [← eq]; simp_rw [← mul_assoc, (he.idem i).eq, mul_assoc, (he.idem i).eq]
    · intro j _ ne; have ⟨r', eq⟩ := (r j).2
      rw [← eq]; simp_rw [← mul_assoc, he.ortho ne.symm, zero_mul]
map_mul' r₁ r₂ := funext fun i => Subtype.ext
    calc e i * (r₁ * r₂) * e i
     _ = e i * (r₁ * e i * r₂) * e i := by
       simp_rw [← ((hc i).comm r₁).eq, ← mul_assoc, (he.idem i).eq]
     _ = e i * r₁ * e i * (e i * r₂ * e i) := by
      conv in (r₁ * _ * r₂) => rw [← (he.idem i).eq]
      simp_rw [mul_assoc]
map_add' r₁ r₂ := funext fun i => Subtype.ext by simpa [mul_add] using! add_mul ..
-/
def CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral [Semiring R]
    (he : CompleteOrthogonalIdempotents e) (hc : forall i, IsMulCentral (e i)) :
    R ≃+* Π i, (he.idem i).Corner where
  toFun r i := ⟨_, r, rfl⟩
  invFun r := ∑ i, (r i).1
  left_inv r := by
    simp_rw [((hc _).comm _).eq, mul_assoc, (he.idem _).eq, ← Finset.mul_sum, he.complete, mul_one]
right_inv r := funext fun i => Subtype.ext by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_eq_single i _ (by simp at ·)]
    · have ⟨r', eq⟩ := (r i).2
      rw [← eq]; simp_rw [← mul_assoc, (he.idem i).eq, mul_assoc, (he.idem i).eq]
    · intro j _ ne; have ⟨r', eq⟩ := (r j).2
      rw [← eq]; simp_rw [← mul_assoc, he.ortho ne.symm, zero_mul]
map_mul' r₁ r₂ := funext fun i => Subtype.ext
    calc e i * (r₁ * r₂) * e i
     _ = e i * (r₁ * e i * r₂) * e i := by
       simp_rw [← ((hc i).comm r₁).eq, ← mul_assoc, (he.idem i).eq]
     _ = e i * r₁ * e i * (e i * r₂ * e i) := by
      conv in (r₁ * _ * r₂) => rw [← (he.idem i).eq]
      simp_rw [mul_assoc]
map_add' r₁ r₂ := funext fun i => Subtype.ext by simpa [mul_add] using! add_mul ..

/--
Definition of `CompleteOrthogonalIdempotents.ringEquivOfComm` / `CompleteOrthogonalIdempotents.ringEquivOfComm` 的定义

English:
definition CompleteOrthogonalIdempotents.ringEquivOfComm
  signature: [CommSemiring R]
  body: he.ringEquivOfIsMulCentral fun _ => Semigroup.mem_center_iff.mpr fun _ => mul_comm ..

中文:
定义 余mpleteOrthogonalIdempotents.ringEquivOfComm
  签名: [交换半环 R]
  定义体: he.ringEquivOfIsMulCentral fun _ => Semigroup.mem_center_iff.mpr fun _ => mul_comm ..

Depends on / 依赖: Semigroup, Semigroup.mem_center_iff.mpr, he.ringEquivOfIsMulCentral, mem_center_iff, mul_comm, ringEquivOfIsMulCentral
-/
def CompleteOrthogonalIdempotents.ringEquivOfComm [CommSemiring R]
    (he : CompleteOrthogonalIdempotents e) : R ≃+* Π i, (he.idem i).Corner :=
  he.ringEquivOfIsMulCentral fun _ => Semigroup.mem_center_iff.mpr fun _ => mul_comm ..

/--
lemma `Ideal.mem_map_span_singleton_iff_of_isIdempotentElem` / 引理 `Ideal.mem_map_span_singleton_iff_of_isIdempotentElem`

English:
lemma Ideal.mem_map_span_singleton_iff_of_isIdempotentElem
  proof: by
  simp only [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton]
  refine ⟨?_, fun H => ⟨_, H, by simp [sub_mul]⟩⟩
  intro ⟨s, hs, t, hrst⟩
  convert I.mul_mem_left (1 - e) hs using 1
  linear_combination he.eq * t - (1 - e) * hrst

中文:
引理 理想.mem_map_span_singleton_iff_of_isIdempotentElem
  证明: by
  simp only [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton]
  refine ⟨?_, fun H => ⟨_, H, by simp [sub_mul]⟩⟩
  intro ⟨s, hs, t, hrst⟩
  convert I.mul_mem_left (1 - e) hs using 1
  linear_combination he.eq * t - (1 - e) * hrst

Depends on / 依赖: I.mul_mem_left, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.Quotient.mk_surjective, Ideal.mem_map_iff_of_surjective, Ideal.mem_span_singleton, Quotient, convert, he.eq, linear_combination, mem_map_iff_of_surjective, mem_span_singleton, mk_eq_mk_iff_sub_mem, mk_surjective, mul_mem_left, sub_mul
-/
lemma Ideal.mem_map_span_singleton_iff_of_isIdempotentElem
    [CommRing R] {e r : R} (he : IsIdempotentElem e) {I : Ideal R} :
    Ideal.Quotient.mk _ r in I.map (Ideal.Quotient.mk (Ideal.span {e})) ↔ (1 - e) * r in I := by
  simp only [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton]
  refine ⟨?_, fun H => ⟨_, H, by simp [sub_mul]⟩⟩
  intro ⟨s, hs, t, hrst⟩
  convert I.mul_mem_left (1 - e) hs using 1
  linear_combination he.eq * t - (1 - e) * hrst

end corner
