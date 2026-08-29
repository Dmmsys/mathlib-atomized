/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Results about big operators with values in a (semi)ring

We prove results about big operators that involve some interaction between
multiplicative and additive structures on the values being combined.
-/

public section

assert_not_exists Field

open Fintype

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

namespace Finset

/--
lemma `prod_neg` / 引理 `prod_neg`

English:
lemma prod_neg
  given: [CommMonoid M] [HasDistribNeg M] (f : ι -> M)
  proof: by
  simpa using (s.1.map f).prod_map_neg

中文:
引理 prod_neg
  条件: [CommMonoid M] [HasDistribNeg M] (f : ι -> M)
  证明: by
  simpa using (s.1.map f).prod_map_neg

Depends on / 依赖: prod_map_neg
-/
lemma prod_neg [CommMonoid M] [HasDistribNeg M] (f : ι -> M) :
    ∏ x in s, -f x = (-1) ^ #s * ∏ x in s, f x := by
  simpa using (s.1.map f).prod_map_neg

section AddCommMonoidWithOne
variable [AddCommMonoidWithOne R]

/--
lemma `natCast_card_filter` / 引理 `natCast_card_filter`

English:
lemma natCast_card_filter
  given: (p) [DecidablePred p] (s : Finset ι)
  proof: by
  rw [sum_ite]; rw [sum_const_zero]; rw [add_zero]; rw [sum_const]; rw [nsmul_one]

中文:
引理 natCast_card_filter
  条件: (p) [DecidablePred p] (s : Finset ι)
  证明: by
  rw [sum_ite]; rw [sum_const_zero]; rw [add_zero]; rw [sum_const]; rw [nsmul_one]

Depends on / 依赖: add_zero, nsmul_one, sum_const, sum_const_zero, sum_ite
-/
lemma natCast_card_filter (p) [DecidablePred p] (s : Finset ι) :
    (#{x in s | p x} : R) = ∑ a in s, if p a then (1 : R) else 0 := by
  rw [sum_ite]; rw [sum_const_zero]; rw [add_zero]; rw [sum_const]; rw [nsmul_one]

/--
lemma `sum_boole` / 引理 `sum_boole`

English:
lemma sum_boole
  given: (p) [DecidablePred p] (s : Finset ι)
  proof: (natCast_card_filter _ _).symm

中文:
引理 sum_boole
  条件: (p) [DecidablePred p] (s : Finset ι)
  证明: (natCast_card_filter _ _).symm
-/
@[simp] lemma sum_boole (p) [DecidablePred p] (s : Finset ι) :
    (∑ x in s, if p x then 1 else 0 : R) = #{x in s | p x} :=
  (natCast_card_filter _ _).symm

/--
lemma `card_eq_sum_ite` / 引理 `card_eq_sum_ite`

English:
lemma card_eq_sum_ite
  given: {s t : Finset ι} [DecidablePred (· in s)] (hst : s subseteq t)
  proof: by simp [hst]

中文:
引理 card_eq_sum_ite
  条件: {s t : Finset ι} [DecidablePred (· in s)] (hst : s subseteq t)
  证明: by simp [hst]
-/
lemma card_eq_sum_ite {s t : Finset ι} [DecidablePred (· in s)] (hst : s subseteq t) :
    s.card = ∑ i in t, if i in s then 1 else 0 := by simp [hst]

end AddCommMonoidWithOne

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

/--
lemma `sum_mul` / 引理 `sum_mul`

English:
lemma sum_mul
  given: (s : Finset ι) (f : ι -> R) (a : R)
  proof: map_sum (AddMonoidHom.mulRight a) _ s

中文:
引理 sum_mul
  条件: (s : Finset ι) (f : ι -> R) (a : R)
  证明: map_sum (AddMonoidHom.mulRight a) _ s

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulRight, map_sum, mulRight
-/
lemma sum_mul (s : Finset ι) (f : ι -> R) (a : R) :
    (∑ i in s, f i) * a = ∑ i in s, f i * a := map_sum (AddMonoidHom.mulRight a) _ s

/--
lemma `mul_sum` / 引理 `mul_sum`

English:
lemma mul_sum
  given: (s : Finset ι) (f : ι -> R) (a : R)
  proof: map_sum (AddMonoidHom.mulLeft a) _ s

中文:
引理 mul_sum
  条件: (s : Finset ι) (f : ι -> R) (a : R)
  证明: map_sum (AddMonoidHom.mulLeft a) _ s

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulLeft, map_sum, mulLeft
-/
lemma mul_sum (s : Finset ι) (f : ι -> R) (a : R) :
    a * ∑ i in s, f i = ∑ i in s, a * f i := map_sum (AddMonoidHom.mulLeft a) _ s

/--
lemma `sum_mul_sum` / 引理 `sum_mul_sum`

English:
lemma sum_mul_sum
  given: (s : Finset ι) (t : Finset κ) (f : ι -> R) (g : κ -> R)
  proof: by
  simp_rw [sum_mul, ← mul_sum]

中文:
引理 sum_mul_sum
  条件: (s : Finset ι) (t : Finset κ) (f : ι -> R) (g : κ -> R)
  证明: by
  simp_rw [sum_mul, ← mul_sum]

Depends on / 依赖: mul_sum, simp_rw, sum_mul
-/
lemma sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι -> R) (g : κ -> R) :
    (∑ i in s, f i) * ∑ j in t, g j = ∑ i in s, ∑ j in t, f i * g j := by
  simp_rw [sum_mul, ← mul_sum]

/--
lemma `_root_.Fintype.sum_mul_sum` / 引理 `_root_.Fintype.sum_mul_sum`

English:
lemma _root_.Fintype.sum_mul_sum
  given: [Fintype ι] [Fintype κ] (f : ι -> R) (g : κ -> R)
  proof: Finset.sum_mul_sum _ _ _ _

中文:
引理 _root_.Fintype.sum_mul_sum
  条件: [Fintype ι] [Fintype κ] (f : ι -> R) (g : κ -> R)
  证明: Finset.sum_mul_sum _ _ _ _

Depends on / 依赖: Finset, Finset.sum_mul_sum, sum_mul_sum
-/
lemma _root_.Fintype.sum_mul_sum [Fintype ι] [Fintype κ] (f : ι -> R) (g : κ -> R) :
    (∑ i, f i) * ∑ j, g j = ∑ i, ∑ j, f i * g j :=
  Finset.sum_mul_sum _ _ _ _

/--
lemma `_root_.Commute.sum_right` / 引理 `_root_.Commute.sum_right`

English:
lemma _root_.Commute.sum_right
  statement: (s : Finset ι) (f : ι -> R) (b : R)
  proof: (Commute.multiset_sum_right _ _) fun b hb => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hb
    exact h _ hi

中文:
引理 _root_.Commute.sum_right
  结论: (s : Finset ι) (f : ι -> R) (b : R)
  证明: (Commute.multiset_sum_right _ _) fun b hb => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hb
    exact h _ hi

Depends on / 依赖: Commute, Commute.multiset_sum_right, Multiset, Multiset.mem_map.mp, mem_map, multiset_sum_right
-/
lemma _root_.Commute.sum_right (s : Finset ι) (f : ι -> R) (b : R)
    (h : forall i in s, Commute b (f i)) : Commute b (∑ i in s, f i) :=
  (Commute.multiset_sum_right _ _) fun b hb => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hb
    exact h _ hi

/--
lemma `_root_.Commute.sum_left` / 引理 `_root_.Commute.sum_left`

English:
lemma _root_.Commute.sum_left
  statement: (s : Finset ι) (f : ι -> R) (b : R)
  proof: ((Commute.sum_right _ _ _) fun _i hi => (h _ hi).symm).symm

中文:
引理 _root_.Commute.sum_left
  结论: (s : Finset ι) (f : ι -> R) (b : R)
  证明: ((Commute.sum_right _ _ _) fun _i hi => (h _ hi).symm).symm

Depends on / 依赖: Commute, Commute.sum_right, sum_right
-/
lemma _root_.Commute.sum_left (s : Finset ι) (f : ι -> R) (b : R)
    (h : forall i in s, Commute (f i) b) : Commute (∑ i in s, f i) b :=
  ((Commute.sum_right _ _ _) fun _i hi => (h _ hi).symm).symm

/--
lemma `sum_range_succ_mul_sum_range_succ` / 引理 `sum_range_succ_mul_sum_range_succ`

English:
lemma sum_range_succ_mul_sum_range_succ
  given: (m n : Nat) (f g : Nat -> R)
  proof: by
  simp only [add_mul, mul_add, add_assoc, sum_range_succ]

中文:
引理 sum_range_succ_mul_sum_range_succ
  条件: (m n : 自然数) (f g : 自然数 -> R)
  证明: by
  simp only [add_mul, mul_add, add_assoc, sum_range_succ]

Depends on / 依赖: add_assoc, add_mul, mul_add, sum_range_succ
-/
lemma sum_range_succ_mul_sum_range_succ (m n : Nat) (f g : Nat -> R) :
    (∑ i in range (m + 1), f i) * ∑ i in range (n + 1), g i =
      (∑ i in range m, f i) * ∑ i in range n, g i +
        f m * ∑ i in range n, g i + (∑ i in range m, f i) * g n + f m * g n := by
  simp only [add_mul, mul_add, add_assoc, sum_range_succ]

end NonUnitalNonAssocSemiring

section NonUnitalSemiring
variable [NonUnitalSemiring R] {f : ι -> R} {a : R}

/--
lemma `dvd_sum` / 引理 `dvd_sum`

English:
lemma dvd_sum
  given: (h : forall i in s, a ∣ f i)
  statement: a ∣ ∑ i in s, f i
  proof: Multiset.dvd_sum fun y hy => by rcases Multiset.mem_map.1 hy with ⟨x, hx, rfl⟩; exact h x hx

中文:
引理 dvd_sum
  条件: (h : 对任意 i in s, a ∣ f i)
  结论: a ∣ ∑ i in s, f i
  证明: Multiset.dvd_sum fun y hy => by rcases Multiset.mem_map.1 hy with ⟨x, hx, rfl⟩; exact h x hx

Depends on / 依赖: Multiset, Multiset.dvd_sum, Multiset.mem_map, dvd_sum, mem_map
-/
lemma dvd_sum (h : forall i in s, a ∣ f i) : a ∣ ∑ i in s, f i :=
  Multiset.dvd_sum fun y hy => by rcases Multiset.mem_map.1 hy with ⟨x, hx, rfl⟩; exact h x hx

end NonUnitalSemiring

section NonAssocSemiring
variable [NonAssocSemiring R] [DecidableEq ι]

/--
lemma `sum_mul_boole` / 引理 `sum_mul_boole`

English:
lemma sum_mul_boole
  given: (s : Finset ι) (f : ι -> R) (i : ι)
  proof: by simp

中文:
引理 sum_mul_boole
  条件: (s : Finset ι) (f : ι -> R) (i : ι)
  证明: by simp
-/
lemma sum_mul_boole (s : Finset ι) (f : ι -> R) (i : ι) :
    ∑ j in s, f j * ite (i = j) 1 0 = ite (i in s) (f i) 0 := by simp

/--
lemma `sum_boole_mul` / 引理 `sum_boole_mul`

English:
lemma sum_boole_mul
  given: (s : Finset ι) (f : ι -> R) (i : ι)
  proof: by simp

中文:
引理 sum_boole_mul
  条件: (s : Finset ι) (f : ι -> R) (i : ι)
  证明: by simp
-/
lemma sum_boole_mul (s : Finset ι) (f : ι -> R) (i : ι) :
    ∑ j in s, ite (i = j) 1 0 * f j = ite (i in s) (f i) 0 := by simp

end NonAssocSemiring

section CommSemiring
variable [CommSemiring R]

/--
theorem `prod_add_prod_eq` / 定理 `prod_add_prod_eq`

English:
theorem prod_add_prod_eq
  statement: {s : Finset ι} {i : ι} {f g h : ι -> R} (hi : i in s)
  proof: by
  classical
    simp_rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi, ← h1, right_distrib]
    congr 2 <;> apply prod_congr rfl <;> simpa

中文:
定理 prod_add_prod_eq
  结论: {s : Finset ι} {i : ι} {f g h : ι -> R} (hi : i in s)
  证明: by
  classical
    simp_rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi, ← h1, right_distrib]
    congr 2 <;> apply prod_congr rfl <;> simpa

Depends on / 依赖: classical, prod_congr, prod_eq_mul_prod_sdiff_singleton_of_mem, right_distrib, simp_rw
-/
theorem prod_add_prod_eq {s : Finset ι} {i : ι} {f g h : ι -> R} (hi : i in s)
    (h1 : g i + h i = f i) (h2 : forall j in s, j != i -> g j = f j) (h3 : forall j in s, j != i -> h j = f j) :
    (∏ i in s, g i) + ∏ i in s, h i = ∏ i in s, f i := by
  classical
    simp_rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi, ← h1, right_distrib]
    congr 2 <;> apply prod_congr rfl <;> simpa

section DecidableEq
variable [DecidableEq ι]

/--
lemma `prod_sum` / 引理 `prod_sum`

English:
lemma prod_sum
  given: {κ : ι -> Type*} (s : Finset ι) (t : forall i, Finset (κ i)) (f : forall i, κ i -> R)
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have h₁ : forall x in t a, forall y in t a, x != y ->
      Disjoint (image (Pi.cons s a x) (pi s t)) (image (Pi.cons s a y) (pi s t)) := by
      intro x _ y _ h
      simp only [disjoint_iff_ne, 

中文:
引理 prod_sum
  条件: {κ : ι -> 类型} (s : Finset ι) (t : 对任意 i, Finset (κ i)) (f : 对任意 i, κ i -> R)
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have h₁ : forall x in t a, forall y in t a, x != y ->
      Disjoint (image (Pi.cons s a x) (pi s t)) (image (Pi.cons s a y) (pi s t)) := by
      intro x _ y _ h
      simp only [disjoint_iff_ne, 

Depends on / 依赖: Disjoint, Finset, Finset.induction, Pi.cons, Pi.cons_same, classical, cons_same, disjoint_iff_ne, insert, mem_image, mem_insert_self
-/
lemma prod_sum {κ : ι -> Type*} (s : Finset ι) (t : forall i, Finset (κ i)) (f : forall i, κ i -> R) :
    ∏ a in s, ∑ b in t a, f a b = ∑ p in s.pi t, ∏ x in s.attach, f x.1 (p x.1 x.2) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have h₁ : forall x in t a, forall y in t a, x != y ->
      Disjoint (image (Pi.cons s a x) (pi s t)) (image (Pi.cons s a y) (pi s t)) := by
      intro x _ y _ h
      simp only [disjoint_iff_ne, mem_image]
      rintro _ ⟨p₂, _, eq₂⟩ _ ⟨p₃, _, eq₃⟩ eq
      have : Pi.cons s a x p₂ a (mem_insert_self _ _)
              = Pi.cons s a y p₃ a (mem_insert_self _ _) := by rw [eq₂, eq₃, eq]
      rw [Pi.cons_same]; rw [Pi.cons_same] at this
      exact h this
    rw [prod_insert ha]; rw [pi_insert ha]; rw [ih]; rw [sum_mul]; rw [sum_biUnion h₁]
    refine sum_congr rfl fun b _ => ?_
    have h₂ : forall p₁ in pi s t, forall p₂ in pi s t, Pi.cons s a b p₁ = Pi.cons s a b p₂ -> p₁ = p₂ :=
      fun p₁ _ p₂ _ eq => Pi.cons_injective ha eq
    rw [sum_image h₂]; rw [mul_sum]
    refine sum_congr rfl fun g _ => ?_
    rw [attach_insert]; rw [prod_insert]; rw [prod_image]
    · simp only [Pi.cons_same]
      congr with ⟨v, hv⟩
      congr
      exact (Pi.cons_ne (by rintro rfl; exact ha hv)).symm
    · exact fun _ _ _ _ => Subtype.ext ∘ Subtype.mk.inj
    · simpa only [mem_image, mem_attach, Subtype.mk.injEq, true_and,
        Subtype.exists, exists_prop, exists_eq_right] using ha

/--
lemma `prod_univ_sum` / 引理 `prod_univ_sum`

English:
lemma prod_univ_sum
  given: {κ : ι -> Type*} [Fintype ι] (t : forall i, Finset (κ i)) (f : forall i, κ i -> R)
  proof: by
  simp only [prod_attach_univ, prod_sum, Finset.sum_univ_pi]

中文:
引理 prod_univ_sum
  条件: {κ : ι -> 类型} [Fintype ι] (t : 对任意 i, Finset (κ i)) (f : 对任意 i, κ i -> R)
  证明: by
  simp only [prod_attach_univ, prod_sum, Finset.sum_univ_pi]

Depends on / 依赖: Finset, Finset.sum_univ_pi, prod_attach_univ, prod_sum, sum_univ_pi
-/
lemma prod_univ_sum {κ : ι -> Type*} [Fintype ι] (t : forall i, Finset (κ i)) (f : forall i, κ i -> R) :
    ∏ i, ∑ j in t i, f i j = ∑ x in piFinset t, ∏ i, f i (x i) := by
  simp only [prod_attach_univ, prod_sum, Finset.sum_univ_pi]

/--
lemma `sum_prod_piFinset` / 引理 `sum_prod_piFinset`

English:
lemma sum_prod_piFinset
  given: [Fintype ι] (s : Finset κ) (g : ι -> κ -> R)
  proof: by
  rw [← prod_univ_sum]

中文:
引理 sum_prod_piFinset
  条件: [Fintype ι] (s : Finset κ) (g : ι -> κ -> R)
  证明: by
  rw [← prod_univ_sum]

Depends on / 依赖: prod_univ_sum
-/
lemma sum_prod_piFinset [Fintype ι] (s : Finset κ) (g : ι -> κ -> R) :
    ∑ f in piFinset fun _ : ι => s, ∏ i, g i (f i) = ∏ i, ∑ j in s, g i j := by
  rw [← prod_univ_sum]

/--
lemma `sum_pow'` / 引理 `sum_pow'`

English:
lemma sum_pow'
  given: (s : Finset κ) (f : κ -> R) (n : Nat)
  proof: by
  convert! @prod_univ_sum (Fin n) _ _ _ _ _ (fun _i => s) fun _i d => f d; simp

中文:
引理 sum_pow'
  条件: (s : Finset κ) (f : κ -> R) (n : 自然数)
  证明: by
  convert! @prod_univ_sum (Fin n) _ _ _ _ _ (fun _i => s) fun _i d => f d; simp

Depends on / 依赖: convert, prod_univ_sum
-/
lemma sum_pow' (s : Finset κ) (f : κ -> R) (n : Nat) :
    (∑ a in s, f a) ^ n = ∑ p in piFinset fun _i : Fin n => s, ∏ i, f (p i) := by
  convert! @prod_univ_sum (Fin n) _ _ _ _ _ (fun _i => s) fun _i d => f d; simp

/--
theorem `prod_add` / 定理 `prod_add`

English:
theorem prod_add
  given: (f g : ι -> R) (s : Finset ι)
  proof: by
  classical
  calc
    ∏ i in s, (f i + g i) =
        ∏ i in s, ∑ p in ({True, False} : Finset Prop), if p then f i else g i := by simp
    _ = ∑ p in (s.pi fun _ => {True, False} : Finset (forall a in s, Prop)),
          ∏ a in s.attach, if p a.1 a.2 then f a.1 else g a.1 := prod_sum _ _ _
   

中文:
定理 prod_add
  条件: (f g : ι -> R) (s : Finset ι)
  证明: by
  classical
  calc
    ∏ i in s, (f i + g i) =
        ∏ i in s, ∑ p in ({True, False} : Finset Prop), if p then f i else g i := by simp
    _ = ∑ p in (s.pi fun _ => {True, False} : Finset (forall a in s, Prop)),
          ∏ a in s.attach, if p a.1 a.2 then f a.1 else g a.1 := prod_sum _ _ _
   

Depends on / 依赖: Classical, Classical.em, Finset, attach, classical, eq_iff_iff, funext_iff, mem_filter, mem_p, powerset, prod_sum, s.attach, s.pi, s.powerset, simp_rw, sum_bij
-/
theorem prod_add (f g : ι -> R) (s : Finset ι) :
    ∏ i in s, (f i + g i) = ∑ t in s.powerset, (∏ i in t, f i) * ∏ i in s \ t, g i := by
  classical
  calc
    ∏ i in s, (f i + g i) =
        ∏ i in s, ∑ p in ({True, False} : Finset Prop), if p then f i else g i := by simp
    _ = ∑ p in (s.pi fun _ => {True, False} : Finset (forall a in s, Prop)),
          ∏ a in s.attach, if p a.1 a.2 then f a.1 else g a.1 := prod_sum _ _ _
    _ = ∑ t in s.powerset, (∏ a in t, f a) * ∏ a in s \ t, g a :=
      sum_bij'
        (fun f _ => {a in s | exists h : a in s, f a h})
        (fun t _ a _ => a in t)
        (by simp)
        (by simp [Classical.em])
        (by simp_rw [mem_filter, funext_iff, eq_iff_iff, mem_pi, mem_insert]; tauto)
        (by simp_rw [Finset.ext_iff, mem_filter, mem_powerset]; tauto)
        (fun a _ => by
          simp only [prod_ite, filter_attach', prod_map, Function.Embedding.coeFn_mk,
            Subtype.map_coe, id_eq, prod_attach]
          congr 2 with x
          simp only [mem_filter, mem_sdiff, not_and, not_exists, and_congr_right_iff]
          tauto)

end DecidableEq

/--
theorem `prod_one_add` / 定理 `prod_one_add`

English:
theorem prod_one_add
  given: {f : ι -> R} (s : Finset ι)
  proof: by
  classical simp only [add_comm (1 : R), prod_add, prod_const_one, mul_one]

中文:
定理 prod_one_add
  条件: {f : ι -> R} (s : Finset ι)
  证明: by
  classical simp only [add_comm (1 : R), prod_add, prod_const_one, mul_one]

Depends on / 依赖: add_comm, classical, mul_one, prod_add, prod_const_one
-/
theorem prod_one_add {f : ι -> R} (s : Finset ι) :
    ∏ i in s, (1 + f i) = ∑ t in s.powerset, ∏ i in t, f i := by
  classical simp only [add_comm (1 : R), prod_add, prod_const_one, mul_one]

/--
theorem `prod_add_one` / 定理 `prod_add_one`

English:
theorem prod_add_one
  given: {f : ι -> R} (s : Finset ι)
  proof: by
  classical simp only [prod_add, prod_const_one, mul_one]

中文:
定理 prod_add_one
  条件: {f : ι -> R} (s : Finset ι)
  证明: by
  classical simp only [prod_add, prod_const_one, mul_one]

Depends on / 依赖: classical, mul_one, prod_add, prod_const_one
-/
theorem prod_add_one {f : ι -> R} (s : Finset ι) :
    ∏ i in s, (f i + 1) = ∑ t in s.powerset, ∏ i in t, f i := by
  classical simp only [prod_add, prod_const_one, mul_one]

/--
theorem `prod_add_ordered` / 定理 `prod_add_ordered`

English:
theorem prod_add_ordered
  given: [LinearOrder ι] (s : Finset ι) (f g : ι -> R)
  proof: by
  refine Finset.induction_on_max s (by simp) ?_
  clear s
  intro a s ha ihs
  have ha' : a ∉ s := fun ha' => lt_irrefl a (ha a ha')
  rw [prod_insert ha']; rw [prod_insert ha']; rw [sum_insert ha']; rw [filter_insert]; rw [if_neg (lt_irrefl a)]; rw [filter_true_of_mem ha]; rw [ihs]; rw [add_mul]

中文:
定理 prod_add_ordered
  条件: [LinearOrder ι] (s : Finset ι) (f g : ι -> R)
  证明: by
  refine Finset.induction_on_max s (by simp) ?_
  clear s
  intro a s ha ihs
  have ha' : a ∉ s := fun ha' => lt_irrefl a (ha a ha')
  rw [prod_insert ha']; rw [prod_insert ha']; rw [sum_insert ha']; rw [filter_insert]; rw [if_neg (lt_irrefl a)]; rw [filter_true_of_mem ha]; rw [ihs]; rw [add_mul]

Depends on / 依赖: Finset, Finset.induction_on_max, add_assoc, add_comm, add_mul, filter_false_of_mem, filter_insert, filter_true_of_mem, forall_mem_insert, if_neg, induction_on_max, lt_irrefl, mul_add, mul_one, not_gt, prod_empty, prod_insert, sum_insert
-/
theorem prod_add_ordered [LinearOrder ι] (s : Finset ι) (f g : ι -> R) :
    ∏ i in s, (f i + g i) =
      (∏ i in s, f i) +
        ∑ i in s, g i * (∏ j in s with j < i, (f j + g j)) * ∏ j in s with i < j, f j := by
  refine Finset.induction_on_max s (by simp) ?_
  clear s
  intro a s ha ihs
  have ha' : a ∉ s := fun ha' => lt_irrefl a (ha a ha')
  rw [prod_insert ha']; rw [prod_insert ha']; rw [sum_insert ha']; rw [filter_insert]; rw [if_neg (lt_irrefl a)]; rw [filter_true_of_mem ha]; rw [ihs]; rw [add_mul]; rw [mul_add]; rw [mul_add]; rw [add_assoc]
  congr 1
  rw [add_comm]
  congr 1
  · rw [filter_false_of_mem, prod_empty, mul_one]
    exact (forall_mem_insert _ _ _).2 ⟨lt_irrefl a, fun i hi => (ha i hi).not_gt⟩
  · rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [filter_insert]; rw [if_neg (ha i hi).not_gt]; rw [filter_insert]; rw [if_pos (ha i hi)]; rw [prod_insert]; rw [mul_left_comm]
    exact mt (fun ha => (mem_filter.1 ha).1) ha'

/--
theorem `prod_one_add_ordered` / 定理 `prod_one_add_ordered`

English:
theorem prod_one_add_ordered
  given: [LinearOrder ι] (s : Finset ι) (f : ι -> R)
  proof: by
  rw [prod_add_ordered]
  simp

中文:
定理 prod_one_add_ordered
  条件: [LinearOrder ι] (s : Finset ι) (f : ι -> R)
  证明: by
  rw [prod_add_ordered]
  simp

Depends on / 依赖: prod_add_ordered
-/
theorem prod_one_add_ordered [LinearOrder ι] (s : Finset ι) (f : ι -> R) :
    ∏ i in s, (1 + f i) = 1 + ∑ i in s, f i * ∏ j in s with j < i, (1 + f j) := by
  rw [prod_add_ordered]
  simp

/--
theorem `sum_pow_mul_eq_add_pow` / 定理 `sum_pow_mul_eq_add_pow`

English:
theorem sum_pow_mul_eq_add_pow
  given: (a b : R) (s : Finset ι)
  proof: by
  classical
  rw [← prod_const]; rw [prod_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [prod_const]; rw [prod_const]; rw [← card_sdiff_of_subset (mem_powerset.1 ht)]

中文:
定理 sum_pow_mul_eq_add_pow
  条件: (a b : R) (s : Finset ι)
  证明: by
  classical
  rw [← prod_const]; rw [prod_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [prod_const]; rw [prod_const]; rw [← card_sdiff_of_subset (mem_powerset.1 ht)]

Depends on / 依赖: Finset, Finset.sum_congr, card_sdiff_of_subset, classical, mem_powerset, prod_add, prod_const, sum_congr
-/
theorem sum_pow_mul_eq_add_pow (a b : R) (s : Finset ι) :
    (∑ t in s.powerset, a ^ #t * b ^ (#s - #t)) = (a + b) ^ #s := by
  classical
  rw [← prod_const]; rw [prod_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [prod_const]; rw [prod_const]; rw [← card_sdiff_of_subset (mem_powerset.1 ht)]

/--
lemma `_root_.Fintype.sum_pow_mul_eq_add_pow` / 引理 `_root_.Fintype.sum_pow_mul_eq_add_pow`

English:
lemma _root_.Fintype.sum_pow_mul_eq_add_pow
  given: (ι : Type*) [Fintype ι] (a b : R)
  proof: Finset.sum_pow_mul_eq_add_pow _ _ _

@[norm_cast]

中文:
引理 _root_.Fintype.sum_pow_mul_eq_add_pow
  条件: (ι : 类型) [Fintype ι] (a b : R)
  证明: Finset.sum_pow_mul_eq_add_pow _ _ _

@[norm_cast]

Depends on / 依赖: Finset, Finset.sum_pow_mul_eq_add_pow, sum_pow_mul_eq_add_pow
-/
lemma _root_.Fintype.sum_pow_mul_eq_add_pow (ι : Type*) [Fintype ι] (a b : R) :
    ∑ s : Finset ι, a ^ #s * b ^ (Fintype.card ι - #s) = (a + b) ^ Fintype.card ι :=
  Finset.sum_pow_mul_eq_add_pow _ _ _

@[norm_cast]
/--
theorem `prod_natCast` / 定理 `prod_natCast`

English:
theorem prod_natCast
  given: (s : Finset ι) (f : ι -> Nat)
  statement: ↑(∏ i in s, f i : Nat) = ∏ i in s, (f i : R)
  proof: map_prod (Nat.castRingHom R) f s

中文:
定理 prod_natCast
  条件: (s : Finset ι) (f : ι -> 自然数)
  结论: ↑(∏ i in s, f i : 自然数) = ∏ i in s, (f i : R)
  证明: map_prod (Nat.castRingHom R) f s

Depends on / 依赖: Nat.castRingHom, castRingHom, map_prod
-/
theorem prod_natCast (s : Finset ι) (f : ι -> Nat) : ↑(∏ i in s, f i : Nat) = ∏ i in s, (f i : R) :=
  map_prod (Nat.castRingHom R) f s

end CommSemiring

section CommRing
variable [CommRing R]

/--
lemma `prod_sub` / 引理 `prod_sub`

English:
lemma prod_sub
  given: [DecidableEq ι] (f g : ι -> R) (s : Finset ι)
  proof: by
  simp [sub_eq_neg_add, prod_add, prod_neg, mul_right_comm]

中文:
引理 prod_sub
  条件: [DecidableEq ι] (f g : ι -> R) (s : Finset ι)
  证明: by
  simp [sub_eq_neg_add, prod_add, prod_neg, mul_right_comm]

Depends on / 依赖: mul_right_comm, prod_add, prod_neg, sub_eq_neg_add
-/
lemma prod_sub [DecidableEq ι] (f g : ι -> R) (s : Finset ι) :
    ∏ i in s, (f i - g i) = ∑ t in s.powerset, (-1) ^ #t * (∏ i in s \ t, f i) * ∏ i in t, g i := by
  simp [sub_eq_neg_add, prod_add, prod_neg, mul_right_comm]

/--
lemma `prod_sub_ordered` / 引理 `prod_sub_ordered`

English:
lemma prod_sub_ordered
  given: [LinearOrder ι] (s : Finset ι) (f g : ι -> R)
  proof: by
  simp only [sub_eq_add_neg]
  convert! prod_add_ordered s f fun i => -g i
  simp

中文:
引理 prod_sub_ordered
  条件: [LinearOrder ι] (s : Finset ι) (f g : ι -> R)
  证明: by
  simp only [sub_eq_add_neg]
  convert! prod_add_ordered s f fun i => -g i
  simp

Depends on / 依赖: convert, prod_add_ordered, sub_eq_add_neg
-/
lemma prod_sub_ordered [LinearOrder ι] (s : Finset ι) (f g : ι -> R) :
    ∏ i in s, (f i - g i) =
      (∏ i in s, f i) -
        ∑ i in s, g i * (∏ j in s with j < i, (f j - g j)) * ∏ j in s with i < j, f j := by
  simp only [sub_eq_add_neg]
  convert! prod_add_ordered s f fun i => -g i
  simp

/--
theorem `prod_one_sub_ordered` / 定理 `prod_one_sub_ordered`

English:
theorem prod_one_sub_ordered
  given: [LinearOrder ι] (s : Finset ι) (f : ι -> R)
  proof: by
  rw [prod_sub_ordered]
  simp

中文:
定理 prod_one_sub_ordered
  条件: [LinearOrder ι] (s : Finset ι) (f : ι -> R)
  证明: by
  rw [prod_sub_ordered]
  simp

Depends on / 依赖: prod_sub_ordered
-/
theorem prod_one_sub_ordered [LinearOrder ι] (s : Finset ι) (f : ι -> R) :
    ∏ i in s, (1 - f i) = 1 - ∑ i in s, f i * ∏ j in s with j < i, (1 - f j) := by
  rw [prod_sub_ordered]
  simp

/--
theorem `prod_range_natCast_sub` / 定理 `prod_range_natCast_sub`

English:
theorem prod_range_natCast_sub
  given: (n k : Nat)
  proof: by
  rw [prod_natCast]
  rcases le_or_gt k n with hkn | hnk
  · exact prod_congr rfl fun i hi => (Nat.cast_sub <| (mem_range.1 hi).le.trans hkn).symm
  · rw [← mem_range] at hnk
    rw [prod_eq_zero hnk]; rw [prod_eq_zero hnk] <;> simp

中文:
定理 prod_range_natCast_sub
  条件: (n k : 自然数)
  证明: by
  rw [prod_natCast]
  rcases le_or_gt k n with hkn | hnk
  · exact prod_congr rfl fun i hi => (Nat.cast_sub <| (mem_range.1 hi).le.trans hkn).symm
  · rw [← mem_range] at hnk
    rw [prod_eq_zero hnk]; rw [prod_eq_zero hnk] <;> simp

Depends on / 依赖: Nat.cast_sub, cast_sub, le.trans, le_or_gt, mem_range, prod_congr, prod_eq_zero, prod_natCast
-/
theorem prod_range_natCast_sub (n k : Nat) :
    ∏ i in range k, (n - i : R) = (∏ i in range k, (n - i) : Nat) := by
  rw [prod_natCast]
  rcases le_or_gt k n with hkn | hnk
  · exact prod_congr rfl fun i hi => (Nat.cast_sub <| (mem_range.1 hi).le.trans hkn).symm
  · rw [← mem_range] at hnk
    rw [prod_eq_zero hnk]; rw [prod_eq_zero hnk] <;> simp

end CommRing
end Finset

open Finset

namespace Fintype
variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]

/--
lemma `sum_pow` / 引理 `sum_pow`

English:
lemma sum_pow
  given: (f : ι -> R) (n : Nat)
  statement: (∑ a, f a) ^ n = ∑ p : Fin n -> ι, ∏ i, f (p i)
  proof: by
  simp [sum_pow']

中文:
引理 sum_pow
  条件: (f : ι -> R) (n : 自然数)
  结论: (∑ a, f a) ^ n = ∑ p : Fin n -> ι, ∏ i, f (p i)
  证明: by
  simp [sum_pow']

Depends on / 依赖: sum_pow
-/
lemma sum_pow (f : ι -> R) (n : Nat) : (∑ a, f a) ^ n = ∑ p : Fin n -> ι, ∏ i, f (p i) := by
  simp [sum_pow']

variable [DecidableEq ι]

/--
lemma `prod_sum` / 引理 `prod_sum`

English:
lemma prod_sum
  given: {κ : ι -> Type*} [forall i, Fintype (κ i)] (f : forall i, κ i -> R)
  proof: Finset.prod_univ_sum _ _

中文:
引理 prod_sum
  条件: {κ : ι -> 类型} [对任意 i, Fintype (κ i)] (f : 对任意 i, κ i -> R)
  证明: Finset.prod_univ_sum _ _

Depends on / 依赖: Finset, Finset.prod_univ_sum, prod_univ_sum
-/
lemma prod_sum {κ : ι -> Type*} [forall i, Fintype (κ i)] (f : forall i, κ i -> R) :
    ∏ i, ∑ j, f i j = ∑ x : forall i, κ i, ∏ i, f i (x i) := Finset.prod_univ_sum _ _

/--
lemma `prod_add` / 引理 `prod_add`

English:
lemma prod_add
  given: (f g : ι -> R)
  statement: ∏ a, (f a + g a) = ∑ t, (∏ a in t, f a) * ∏ a in tᶜ, g a
  proof: by
  simpa [compl_eq_univ_sdiff] using Finset.prod_add f g univ

中文:
引理 prod_add
  条件: (f g : ι -> R)
  结论: ∏ a, (f a + g a) = ∑ t, (∏ a in t, f a) * ∏ a in tᶜ, g a
  证明: by
  simpa [compl_eq_univ_sdiff] using Finset.prod_add f g univ

Depends on / 依赖: Finset, Finset.prod_add, compl_eq_univ_sdiff, prod_add
-/
lemma prod_add (f g : ι -> R) : ∏ a, (f a + g a) = ∑ t, (∏ a in t, f a) * ∏ a in tᶜ, g a := by
  simpa [compl_eq_univ_sdiff] using Finset.prod_add f g univ

end Fintype

namespace Nat
variable {ι : Type*} {s : Finset ι} {f : ι -> Nat} {n : Nat}

/--
lemma `sum_div` / 引理 `sum_div`

English:
lemma sum_div
  given: (hf : forall i in s, n ∣ f i)
  statement: (∑ i in s, f i) / n = ∑ i in s, f i / n
  proof: by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  rw [Nat.div_eq_iff_eq_mul_left hn (dvd_sum hf)]; rw [sum_mul]
  refine sum_congr rfl fun s hs => ?_
  rw [Nat.div_mul_cancel (hf _ hs)]

@[simp, norm_cast]

中文:
引理 sum_div
  条件: (hf : 对任意 i in s, n ∣ f i)
  结论: (∑ i in s, f i) / n = ∑ i in s, f i / n
  证明: by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  rw [Nat.div_eq_iff_eq_mul_left hn (dvd_sum hf)]; rw [sum_mul]
  refine sum_congr rfl fun s hs => ?_
  rw [Nat.div_mul_cancel (hf _ hs)]

@[simp, norm_cast]
-/
protected lemma sum_div (hf : forall i in s, n ∣ f i) : (∑ i in s, f i) / n = ∑ i in s, f i / n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  rw [Nat.div_eq_iff_eq_mul_left hn (dvd_sum hf)]; rw [sum_mul]
  refine sum_congr rfl fun s hs => ?_
  rw [Nat.div_mul_cancel (hf _ hs)]

@[simp, norm_cast]
/--
lemma `cast_list_sum` / 引理 `cast_list_sum`

English:
lemma cast_list_sum
  given: [AddMonoidWithOne R] (s : List Nat)
  statement: (↑s.sum : R) = (s.map (↑)).sum
  proof: map_list_sum (castAddMonoidHom R) _

@[simp, norm_cast]

中文:
引理 cast_list_sum
  条件: [AddMonoidWithOne R] (s : List 自然数)
  结论: (↑s.sum : R) = (s.map (↑)).sum
  证明: map_list_sum (castAddMonoidHom R) _

@[simp, norm_cast]

Depends on / 依赖: castAddMonoidHom, map_list_sum
-/
lemma cast_list_sum [AddMonoidWithOne R] (s : List Nat) : (↑s.sum : R) = (s.map (↑)).sum :=
  map_list_sum (castAddMonoidHom R) _

@[simp, norm_cast]
/--
lemma `cast_list_prod` / 引理 `cast_list_prod`

English:
lemma cast_list_prod
  given: [Semiring R] (s : List Nat)
  statement: (↑s.prod : R) = (s.map (↑)).prod
  proof: map_list_prod (castRingHom R) _

@[simp, norm_cast]

中文:
引理 cast_list_prod
  条件: [Semiring R] (s : List 自然数)
  结论: (↑s.prod : R) = (s.map (↑)).prod
  证明: map_list_prod (castRingHom R) _

@[simp, norm_cast]

Depends on / 依赖: castRingHom, map_list_prod
-/
lemma cast_list_prod [Semiring R] (s : List Nat) : (↑s.prod : R) = (s.map (↑)).prod :=
  map_list_prod (castRingHom R) _

@[simp, norm_cast]
/--
lemma `cast_multiset_sum` / 引理 `cast_multiset_sum`

English:
lemma cast_multiset_sum
  given: [AddCommMonoidWithOne R] (s : Multiset Nat)
  proof: map_multiset_sum (castAddMonoidHom R) _

@[simp, norm_cast]

中文:
引理 cast_multiset_sum
  条件: [AddCommMonoidWithOne R] (s : Multiset 自然数)
  证明: map_multiset_sum (castAddMonoidHom R) _

@[simp, norm_cast]

Depends on / 依赖: castAddMonoidHom, map_multiset_sum
-/
lemma cast_multiset_sum [AddCommMonoidWithOne R] (s : Multiset Nat) :
    (↑s.sum : R) = (s.map (↑)).sum :=
  map_multiset_sum (castAddMonoidHom R) _

@[simp, norm_cast]
/--
lemma `cast_multiset_prod` / 引理 `cast_multiset_prod`

English:
lemma cast_multiset_prod
  given: [CommSemiring R] (s : Multiset Nat)
  statement: (↑s.prod : R) = (s.map (↑)).prod
  proof: map_multiset_prod (castRingHom R) _

@[simp, norm_cast]

中文:
引理 cast_multiset_prod
  条件: [CommSemiring R] (s : Multiset 自然数)
  结论: (↑s.prod : R) = (s.map (↑)).prod
  证明: map_multiset_prod (castRingHom R) _

@[simp, norm_cast]

Depends on / 依赖: castRingHom, map_multiset_prod
-/
lemma cast_multiset_prod [CommSemiring R] (s : Multiset Nat) : (↑s.prod : R) = (s.map (↑)).prod :=
  map_multiset_prod (castRingHom R) _

@[simp, norm_cast]
/--
lemma `cast_sum` / 引理 `cast_sum`

English:
lemma cast_sum
  given: [AddCommMonoidWithOne R] (s : Finset ι) (f : ι -> Nat)
  proof: map_sum (castAddMonoidHom R) _ _

@[simp, norm_cast]

中文:
引理 cast_sum
  条件: [AddCommMonoidWithOne R] (s : Finset ι) (f : ι -> 自然数)
  证明: map_sum (castAddMonoidHom R) _ _

@[simp, norm_cast]

Depends on / 依赖: castAddMonoidHom, map_sum
-/
lemma cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι -> Nat) :
    ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R) :=
  map_sum (castAddMonoidHom R) _ _

@[simp, norm_cast]
/--
lemma `cast_prod` / 引理 `cast_prod`

English:
lemma cast_prod
  given: [CommSemiring R] (f : ι -> Nat) (s : Finset ι)
  proof: map_prod (castRingHom R) _ _

中文:
引理 cast_prod
  条件: [CommSemiring R] (f : ι -> 自然数) (s : Finset ι)
  证明: map_prod (castRingHom R) _ _

Depends on / 依赖: castRingHom, map_prod
-/
lemma cast_prod [CommSemiring R] (f : ι -> Nat) (s : Finset ι) :
    (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R) :=
  map_prod (castRingHom R) _ _

end Nat

namespace Int
variable {ι : Type*} {s : Finset ι} {f : ι -> Int} {n : Int}

/--
lemma `sum_div` / 引理 `sum_div`

English:
lemma sum_div
  given: (hf : forall i in s, n ∣ f i)
  statement: (∑ i in s, f i) / n = ∑ i in s, f i / n
  proof: by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [Int.ediv_eq_iff_eq_mul_left hn (dvd_sum hf)]; rw [sum_mul]
  refine sum_congr rfl fun s hs => ?_
  rw [Int.ediv_mul_cancel (hf _ hs)]

@[simp, norm_cast]

中文:
引理 sum_div
  条件: (hf : 对任意 i in s, n ∣ f i)
  结论: (∑ i in s, f i) / n = ∑ i in s, f i / n
  证明: by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [Int.ediv_eq_iff_eq_mul_left hn (dvd_sum hf)]; rw [sum_mul]
  refine sum_congr rfl fun s hs => ?_
  rw [Int.ediv_mul_cancel (hf _ hs)]

@[simp, norm_cast]
-/
protected lemma sum_div (hf : forall i in s, n ∣ f i) : (∑ i in s, f i) / n = ∑ i in s, f i / n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [Int.ediv_eq_iff_eq_mul_left hn (dvd_sum hf)]; rw [sum_mul]
  refine sum_congr rfl fun s hs => ?_
  rw [Int.ediv_mul_cancel (hf _ hs)]

@[simp, norm_cast]
/--
lemma `cast_list_sum` / 引理 `cast_list_sum`

English:
lemma cast_list_sum
  given: [AddGroupWithOne R] (s : List Int)
  statement: (↑s.sum : R) = (s.map (↑)).sum
  proof: map_list_sum (castAddHom R) _

@[simp, norm_cast]

中文:
引理 cast_list_sum
  条件: [AddGroupWithOne R] (s : List 整数)
  结论: (↑s.sum : R) = (s.map (↑)).sum
  证明: map_list_sum (castAddHom R) _

@[simp, norm_cast]

Depends on / 依赖: castAddHom, map_list_sum
-/
lemma cast_list_sum [AddGroupWithOne R] (s : List Int) : (↑s.sum : R) = (s.map (↑)).sum :=
  map_list_sum (castAddHom R) _

@[simp, norm_cast]
/--
lemma `cast_list_prod` / 引理 `cast_list_prod`

English:
lemma cast_list_prod
  given: [Ring R] (s : List Int)
  statement: (↑s.prod : R) = (s.map (↑)).prod
  proof: map_list_prod (castRingHom R) _

@[simp, norm_cast]

中文:
引理 cast_list_prod
  条件: [Ring R] (s : List 整数)
  结论: (↑s.prod : R) = (s.map (↑)).prod
  证明: map_list_prod (castRingHom R) _

@[simp, norm_cast]

Depends on / 依赖: castRingHom, map_list_prod
-/
lemma cast_list_prod [Ring R] (s : List Int) : (↑s.prod : R) = (s.map (↑)).prod :=
  map_list_prod (castRingHom R) _

@[simp, norm_cast]
/--
lemma `cast_multiset_sum` / 引理 `cast_multiset_sum`

English:
lemma cast_multiset_sum
  given: [AddCommGroupWithOne R] (s : Multiset Int)
  proof: map_multiset_sum (castAddHom R) _

@[simp, norm_cast]

中文:
引理 cast_multiset_sum
  条件: [AddCommGroupWithOne R] (s : Multiset 整数)
  证明: map_multiset_sum (castAddHom R) _

@[simp, norm_cast]

Depends on / 依赖: castAddHom, map_multiset_sum
-/
lemma cast_multiset_sum [AddCommGroupWithOne R] (s : Multiset Int) :
    (↑s.sum : R) = (s.map (↑)).sum :=
  map_multiset_sum (castAddHom R) _

@[simp, norm_cast]
/--
lemma `cast_multiset_prod` / 引理 `cast_multiset_prod`

English:
lemma cast_multiset_prod
  given: {R : Type*} [CommRing R] (s : Multiset Int)
  proof: map_multiset_prod (castRingHom R) _

@[simp, norm_cast]

中文:
引理 cast_multiset_prod
  条件: {R : 类型} [CommRing R] (s : Multiset 整数)
  证明: map_multiset_prod (castRingHom R) _

@[simp, norm_cast]

Depends on / 依赖: castRingHom, map_multiset_prod
-/
lemma cast_multiset_prod {R : Type*} [CommRing R] (s : Multiset Int) :
    (↑s.prod : R) = (s.map (↑)).prod :=
  map_multiset_prod (castRingHom R) _

@[simp, norm_cast]
/--
lemma `cast_sum` / 引理 `cast_sum`

English:
lemma cast_sum
  given: [AddCommGroupWithOne R] (s : Finset ι) (f : ι -> Int)
  proof: map_sum (castAddHom R) _ _

@[simp, norm_cast]

中文:
引理 cast_sum
  条件: [AddCommGroupWithOne R] (s : Finset ι) (f : ι -> 整数)
  证明: map_sum (castAddHom R) _ _

@[simp, norm_cast]

Depends on / 依赖: castAddHom, map_sum
-/
lemma cast_sum [AddCommGroupWithOne R] (s : Finset ι) (f : ι -> Int) :
    ↑(∑ x in s, f x : Int) = ∑ x in s, (f x : R) :=
  map_sum (castAddHom R) _ _

@[simp, norm_cast]
/--
lemma `cast_prod` / 引理 `cast_prod`

English:
lemma cast_prod
  given: {R : Type*} [CommRing R] (f : ι -> Int) (s : Finset ι)
  proof: map_prod (Int.castRingHom R) _ _

中文:
引理 cast_prod
  条件: {R : 类型} [CommRing R] (f : ι -> 整数) (s : Finset ι)
  证明: map_prod (Int.castRingHom R) _ _

Depends on / 依赖: Int.castRingHom, castRingHom, map_prod
-/
lemma cast_prod {R : Type*} [CommRing R] (f : ι -> Int) (s : Finset ι) :
    (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R) :=
  map_prod (Int.castRingHom R) _ _

end Int
