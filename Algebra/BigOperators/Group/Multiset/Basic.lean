/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic

/-!
# Sums and products over multisets

In this file we define products and sums indexed by multisets. This is later used to define products
and sums indexed by finite sets.

## Main declarations

* `Multiset.prod`: `s.prod f` is the product of `f i` over all `i ∈ s`. Not to be mistaken with
  the Cartesian product `Multiset.product`.
* `Multiset.sum`: `s.sum f` is the sum of `f i` over all `i ∈ s`.
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {F ι κ G M N O : Type*}

namespace Multiset

section CommMonoid

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι -> M}

@[to_additive (attr := simp)]
/--
theorem `prod_erase` / 定理 `prod_erase`

English:
theorem prod_erase
  given: [DecidableEq M] (h : a in s)
  statement: a * (s.erase a).prod = s.prod
  proof: by
  rw [← s.coe_toList]; rw [coe_erase]; rw [prod_coe]; rw [prod_coe]; rw [List.prod_erase (mem_toList.2 h)]

@[to_additive (attr := simp)]

中文:
定理 prod_erase
  条件: [DecidableEq M] (h : a in s)
  结论: a * (s.erase a).prod = s.prod
  证明: by
  rw [← s.coe_toList]; rw [coe_erase]; rw [prod_coe]; rw [prod_coe]; rw [List.prod_erase (mem_toList.2 h)]

@[to_additive (attr := simp)]

Depends on / 依赖: List.prod_erase, coe_erase, coe_toList, mem_toList, prod_coe, prod_erase, s.coe_toList
-/
theorem prod_erase [DecidableEq M] (h : a in s) : a * (s.erase a).prod = s.prod := by
  rw [← s.coe_toList]; rw [coe_erase]; rw [prod_coe]; rw [prod_coe]; rw [List.prod_erase (mem_toList.2 h)]

@[to_additive (attr := simp)]
/--
theorem `prod_map_erase` / 定理 `prod_map_erase`

English:
theorem prod_map_erase
  given: [DecidableEq ι] {a : ι} (h : a in m)
  proof: by
  rw [← m.coe_toList]; rw [coe_erase]; rw [map_coe]; rw [map_coe]; rw [prod_coe]; rw [prod_coe]; rw [List.prod_map_erase f (mem_toList.2 h)]

@[to_additive (attr := simp, grind =)]

中文:
定理 prod_map_erase
  条件: [DecidableEq ι] {a : ι} (h : a in m)
  证明: by
  rw [← m.coe_toList]; rw [coe_erase]; rw [map_coe]; rw [map_coe]; rw [prod_coe]; rw [prod_coe]; rw [List.prod_map_erase f (mem_toList.2 h)]

@[to_additive (attr := simp, grind =)]

Depends on / 依赖: List.prod_map_erase, coe_erase, coe_toList, m.coe_toList, map_coe, mem_toList, prod_coe, prod_map_erase
-/
theorem prod_map_erase [DecidableEq ι] {a : ι} (h : a in m) :
    f a * ((m.erase a).map f).prod = (m.map f).prod := by
  rw [← m.coe_toList]; rw [coe_erase]; rw [map_coe]; rw [map_coe]; rw [prod_coe]; rw [prod_coe]; rw [List.prod_map_erase f (mem_toList.2 h)]

@[to_additive (attr := simp, grind =)]
/--
theorem `prod_add` / 定理 `prod_add`

English:
theorem prod_add
  given: (s t : Multiset M)
  statement: prod (s + t) = prod s * prod t
  proof: Quotient.inductionOn₂ s t fun l₁ l₂ => by simp [List.prod_append]

@[to_additive]

中文:
定理 prod_add
  条件: (s t : Multiset M)
  结论: prod (s + t) = prod s * prod t
  证明: Quotient.inductionOn₂ s t fun l₁ l₂ => by simp [List.prod_append]

@[to_additive]

Depends on / 依赖: List.prod_append, Quotient, Quotient.inductionOn, prod_append
-/
theorem prod_add (s t : Multiset M) : prod (s + t) = prod s * prod t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ => by simp [List.prod_append]

@[to_additive]
/--
theorem `prod_nsmul` / 定理 `prod_nsmul`

English:
theorem prod_nsmul
  given: (m : Multiset M)
  statement: forall n : Nat, (n • m).prod = m.prod ^ n

中文:
定理 prod_nsmul
  条件: (m : Multiset M)
  结论: 对任意 n : 自然数, (n • m).prod = m.prod ^ n
-/
theorem prod_nsmul (m : Multiset M) : forall n : Nat, (n • m).prod = m.prod ^ n
  | 0 => by
    rw [zero_nsmul]; rw [pow_zero]
    rfl
  | n + 1 => by rw [add_nsmul, one_nsmul, pow_add, pow_one, prod_add, prod_nsmul m n]

@[to_additive]
/--
theorem `prod_filter_mul_prod_filter_not` / 定理 `prod_filter_mul_prod_filter_not`

English:
theorem prod_filter_mul_prod_filter_not
  given: (p) [DecidablePred p]
  proof: by
  rw [← prod_add]; rw [filter_add_not]

@[to_additive]

中文:
定理 prod_filter_mul_prod_filter_not
  条件: (p) [DecidablePred p]
  证明: by
  rw [← prod_add]; rw [filter_add_not]

@[to_additive]

Depends on / 依赖: filter_add_not, prod_add
-/
theorem prod_filter_mul_prod_filter_not (p) [DecidablePred p] :
    (s.filter p).prod * (s.filter (fun a => ¬ p a)).prod = s.prod := by
  rw [← prod_add]; rw [filter_add_not]

@[to_additive]
/--
theorem `prod_map_eq_pow_single` / 定理 `prod_map_eq_pow_single`

English:
theorem prod_map_eq_pow_single
  statement: [DecidableEq ι] (i : ι)
  proof: by
  induction m using Quotient.inductionOn
  simp [List.prod_map_eq_pow_single i f hf]

@[to_additive]

中文:
定理 prod_map_eq_pow_single
  结论: [DecidableEq ι] (i : ι)
  证明: by
  induction m using Quotient.inductionOn
  simp [List.prod_map_eq_pow_single i f hf]

@[to_additive]

Depends on / 依赖: List.prod_map_eq_pow_single, Quotient, Quotient.inductionOn, inductionOn, prod_map_eq_pow_single
-/
theorem prod_map_eq_pow_single [DecidableEq ι] (i : ι)
    (hf : forall i' != i, i' in m -> f i' = 1) : (m.map f).prod = f i ^ m.count i := by
  induction m using Quotient.inductionOn
  simp [List.prod_map_eq_pow_single i f hf]

@[to_additive]
/--
theorem `prod_eq_pow_single` / 定理 `prod_eq_pow_single`

English:
theorem prod_eq_pow_single
  given: [DecidableEq M] (a : M) (h : forall a' != a, a' in s -> a' = 1)
  proof: by
  induction s using Quotient.inductionOn; simp [List.prod_eq_pow_single a h]

@[to_additive]

中文:
定理 prod_eq_pow_single
  条件: [DecidableEq M] (a : M) (h : 对任意 a' != a, a' in s -> a' = 1)
  证明: by
  induction s using Quotient.inductionOn; simp [List.prod_eq_pow_single a h]

@[to_additive]

Depends on / 依赖: List.prod_eq_pow_single, Quotient, Quotient.inductionOn, inductionOn, prod_eq_pow_single
-/
theorem prod_eq_pow_single [DecidableEq M] (a : M) (h : forall a' != a, a' in s -> a' = 1) :
    s.prod = a ^ s.count a := by
  induction s using Quotient.inductionOn; simp [List.prod_eq_pow_single a h]

@[to_additive]
/--
lemma `prod_eq_one` / 引理 `prod_eq_one`

English:
lemma prod_eq_one
  given: (h : forall x in s, x = (1 : M))
  statement: s.prod = 1
  proof: by
  induction s using Quotient.inductionOn; simp [List.prod_eq_one h]

@[to_additive]

中文:
引理 prod_eq_one
  条件: (h : 对任意 x in s, x = (1 : M))
  结论: s.prod = 1
  证明: by
  induction s using Quotient.inductionOn; simp [List.prod_eq_one h]

@[to_additive]

Depends on / 依赖: List.prod_eq_one, Quotient, Quotient.inductionOn, inductionOn, prod_eq_one
-/
lemma prod_eq_one (h : forall x in s, x = (1 : M)) : s.prod = 1 := by
  induction s using Quotient.inductionOn; simp [List.prod_eq_one h]

@[to_additive]
/--
theorem `prod_hom_ne_zero` / 定理 `prod_hom_ne_zero`

English:
theorem prod_hom_ne_zero
  statement: {s : Multiset M} (hs : s != 0) {F : Type*} [FunLike F M N]
  proof: by
  induction s using Quot.inductionOn; aesop (add simp List.prod_hom_nonempty)

@[to_additive]

中文:
定理 prod_hom_ne_zero
  结论: {s : Multiset M} (hs : s != 0) {F : 类型} [FunLike F M N]
  证明: by
  induction s using Quot.inductionOn; aesop (add simp List.prod_hom_nonempty)

@[to_additive]

Depends on / 依赖: List.prod_hom_nonempty, Quot.inductionOn, inductionOn, prod_hom_nonempty
-/
theorem prod_hom_ne_zero {s : Multiset M} (hs : s != 0) {F : Type*} [FunLike F M N]
    [MulHomClass F M N] (f : F) :
    (s.map f).prod = f s.prod := by
  induction s using Quot.inductionOn; aesop (add simp List.prod_hom_nonempty)

@[to_additive]
/--
theorem `prod_hom` / 定理 `prod_hom`

English:
theorem prod_hom
  statement: (s : Multiset M) {F : Type*} [FunLike F M N]
  proof: Quotient.inductionOn s fun l => by simp only [l.prod_hom f, quot_mk_to_coe, map_coe, prod_coe]

@[to_additive]

中文:
定理 prod_hom
  结论: (s : Multiset M) {F : 类型} [FunLike F M N]
  证明: Quotient.inductionOn s fun l => by simp only [l.prod_hom f, quot_mk_to_coe, map_coe, prod_coe]

@[to_additive]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, l.prod_hom, map_coe, prod_coe, prod_hom, quot_mk_to_coe
-/
theorem prod_hom (s : Multiset M) {F : Type*} [FunLike F M N]
    [MonoidHomClass F M N] (f : F) :
    (s.map f).prod = f s.prod :=
  Quotient.inductionOn s fun l => by simp only [l.prod_hom f, quot_mk_to_coe, map_coe, prod_coe]

@[to_additive]
/--
theorem `prod_hom'` / 定理 `prod_hom'`

English:
theorem prod_hom'
  statement: (s : Multiset ι) {F : Type*} [FunLike F M N]
  proof: by
  convert! (s.map g).prod_hom f
  exact (map_map _ _ _).symm

@[to_additive]

中文:
定理 prod_hom'
  结论: (s : Multiset ι) {F : 类型} [FunLike F M N]
  证明: by
  convert! (s.map g).prod_hom f
  exact (map_map _ _ _).symm

@[to_additive]

Depends on / 依赖: convert, map_map, prod_hom, s.map
-/
theorem prod_hom' (s : Multiset ι) {F : Type*} [FunLike F M N]
    [MonoidHomClass F M N] (f : F)
    (g : ι -> M) : (s.map fun i => f <| g i).prod = f (s.map g).prod := by
  convert! (s.map g).prod_hom f
  exact (map_map _ _ _).symm

@[to_additive]
/--
theorem `prod_hom₂_ne_zero` / 定理 `prod_hom₂_ne_zero`

English:
theorem prod_hom₂_ne_zero
  statement: [CommMonoid O] {s : Multiset ι} (hs : s != 0) (f : M -> N -> O)
  proof: by
  induction s using Quotient.inductionOn; aesop (add simp List.prod_hom₂_nonempty)

@[to_additive]

中文:
定理 prod_hom₂_ne_zero
  结论: [CommMonoid O] {s : Multiset ι} (hs : s != 0) (f : M -> N -> O)
  证明: by
  induction s using Quotient.inductionOn; aesop (add simp List.prod_hom₂_nonempty)

@[to_additive]

Depends on / 依赖: List.prod_hom, Quotient, Quotient.inductionOn, inductionOn
-/
theorem prod_hom₂_ne_zero [CommMonoid O] {s : Multiset ι} (hs : s != 0) (f : M -> N -> O)
    (hf : forall a b c d, f (a * b) (c * d) = f a c * f b d) (f₁ : ι -> M) (f₂ : ι -> N) :
    (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod := by
  induction s using Quotient.inductionOn; aesop (add simp List.prod_hom₂_nonempty)

@[to_additive]
/--
theorem `prod_hom₂` / 定理 `prod_hom₂`

English:
theorem prod_hom₂
  statement: [CommMonoid O] (s : Multiset ι) (f : M -> N -> O)
  proof: Quotient.inductionOn s fun l => by
    simp only [l.prod_hom₂ f hf hf', quot_mk_to_coe, map_coe, prod_coe]

@[to_additive (attr := simp)]

中文:
定理 prod_hom₂
  结论: [CommMonoid O] (s : Multiset ι) (f : M -> N -> O)
  证明: Quotient.inductionOn s fun l => by
    simp only [l.prod_hom₂ f hf hf', quot_mk_to_coe, map_coe, prod_coe]

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, l.prod_hom, map_coe, prod_coe, quot_mk_to_coe
-/
theorem prod_hom₂ [CommMonoid O] (s : Multiset ι) (f : M -> N -> O)
    (hf : forall a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1) (f₁ : ι -> M)
    (f₂ : ι -> N) : (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom₂ f hf hf', quot_mk_to_coe, map_coe, prod_coe]

@[to_additive (attr := simp)]
/--
theorem `prod_map_mul` / 定理 `prod_map_mul`

English:
theorem prod_map_mul
  statement: (m.map fun i => f i * g i).prod = (m.map f).prod * (m.map g).prod
  proof: m.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _

@[to_additive]

中文:
定理 prod_map_mul
  结论: (m.map fun i => f i * g i).prod = (m.map f).prod * (m.map g).prod
  证明: m.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _

@[to_additive]

Depends on / 依赖: m.prod_hom, mul_mul_mul_comm, mul_one
-/
theorem prod_map_mul : (m.map fun i => f i * g i).prod = (m.map f).prod * (m.map g).prod :=
  m.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _

@[to_additive]
/--
theorem `prod_map_pow` / 定理 `prod_map_pow`

English:
theorem prod_map_pow
  given: {n : Nat}
  statement: (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n
  proof: m.prod_hom' (powMonoidHom n : M ->* M) f

@[to_additive]

中文:
定理 prod_map_pow
  条件: {n : 自然数}
  结论: (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n
  证明: m.prod_hom' (powMonoidHom n : M ->* M) f

@[to_additive]

Depends on / 依赖: m.prod_hom, powMonoidHom, prod_hom
-/
theorem prod_map_pow {n : Nat} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n :=
  m.prod_hom' (powMonoidHom n : M ->* M) f

@[to_additive]
/--
theorem `prod_map_prod_map` / 定理 `prod_map_prod_map`

English:
theorem prod_map_prod_map
  given: (m : Multiset ι) (n : Multiset κ) {f : ι -> κ -> M}
  proof: Multiset.induction_on m (by simp) fun a m ih => by simp [ih]

中文:
定理 prod_map_prod_map
  条件: (m : Multiset ι) (n : Multiset κ) {f : ι -> κ -> M}
  证明: Multiset.induction_on m (by simp) fun a m ih => by simp [ih]

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on
-/
theorem prod_map_prod_map (m : Multiset ι) (n : Multiset κ) {f : ι -> κ -> M} :
    prod (m.map fun a => prod <| n.map fun b => f a b) =
      prod (n.map fun b => prod <| m.map fun a => f a b) :=
  Multiset.induction_on m (by simp) fun a m ih => by simp [ih]

/--
theorem `prod_dvd_prod_of_le` / 定理 `prod_dvd_prod_of_le`

English:
theorem prod_dvd_prod_of_le
  given: (h : s <= t)
  statement: s.prod ∣ t.prod
  proof: by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  simp only [prod_add, dvd_mul_right]

@[to_additive]

中文:
定理 prod_dvd_prod_of_le
  条件: (h : s <= t)
  结论: s.prod ∣ t.prod
  证明: by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  simp only [prod_add, dvd_mul_right]

@[to_additive]

Depends on / 依赖: dvd_mul_right, exists_add_of_le, prod_add
-/
theorem prod_dvd_prod_of_le (h : s <= t) : s.prod ∣ t.prod := by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  simp only [prod_add, dvd_mul_right]

@[to_additive]
/--
lemma `_root_.map_multiset_prod` / 引理 `_root_.map_multiset_prod`

English:
lemma _root_.map_multiset_prod
  given: [FunLike F M N] [MonoidHomClass F M N] (f : F) (s : Multiset M)
  proof: (s.prod_hom f).symm

@[to_additive]

中文:
引理 _root_.map_multiset_prod
  条件: [FunLike F M N] [MonoidHomClass F M N] (f : F) (s : Multiset M)
  证明: (s.prod_hom f).symm

@[to_additive]

Depends on / 依赖: prod_hom, s.prod_hom
-/
lemma _root_.map_multiset_prod [FunLike F M N] [MonoidHomClass F M N] (f : F) (s : Multiset M) :
    f s.prod = (s.map f).prod := (s.prod_hom f).symm

@[to_additive]
/--
lemma `_root_.map_multiset_ne_zero_prod` / 引理 `_root_.map_multiset_ne_zero_prod`

English:
lemma _root_.map_multiset_ne_zero_prod
  statement: [FunLike F M N] [MulHomClass F M N] (f : F)
  proof: (s.prod_hom_ne_zero hs f).symm

@[to_additive]

中文:
引理 _root_.map_multiset_ne_zero_prod
  结论: [FunLike F M N] [MulHomClass F M N] (f : F)
  证明: (s.prod_hom_ne_zero hs f).symm

@[to_additive]

Depends on / 依赖: prod_hom_ne_zero, s.prod_hom_ne_zero
-/
lemma _root_.map_multiset_ne_zero_prod [FunLike F M N] [MulHomClass F M N] (f : F)
    {s : Multiset M} (hs : s != 0) :
    f s.prod = (s.map f).prod := (s.prod_hom_ne_zero hs f).symm

@[to_additive]
/--
lemma `_root_.MonoidHom.map_multiset_prod` / 引理 `_root_.MonoidHom.map_multiset_prod`

English:
lemma _root_.MonoidHom.map_multiset_prod
  given: (f : M ->* N) (s : Multiset M)
  proof: (s.prod_hom f).symm

@[to_additive]

中文:
引理 _root_.MonoidHom.map_multiset_prod
  条件: (f : M ->* N) (s : Multiset M)
  证明: (s.prod_hom f).symm

@[to_additive]
-/
protected lemma _root_.MonoidHom.map_multiset_prod (f : M ->* N) (s : Multiset M) :
    f s.prod = (s.map f).prod := (s.prod_hom f).symm

@[to_additive]
/--
lemma `_root_.MulHom.map_multiset_ne_zero_prod` / 引理 `_root_.MulHom.map_multiset_ne_zero_prod`

English:
lemma _root_.MulHom.map_multiset_ne_zero_prod
  statement: (f : M ->ₙ* N) (s : Multiset M)
  proof: (s.prod_hom_ne_zero hs f).symm

中文:
引理 _root_.MulHom.map_multiset_ne_zero_prod
  结论: (f : M ->ₙ* N) (s : Multiset M)
  证明: (s.prod_hom_ne_zero hs f).symm
-/
protected lemma _root_.MulHom.map_multiset_ne_zero_prod (f : M ->ₙ* N) (s : Multiset M)
    (hs : s != 0) : f s.prod = (s.map f).prod := (s.prod_hom_ne_zero hs f).symm

/--
lemma `dvd_prod` / 引理 `dvd_prod`

English:
lemma dvd_prod
  statement: a in s -> a ∣ s.prod
  proof: Quotient.inductionOn s (fun l a h => by simpa using List.dvd_prod h) a

中文:
引理 dvd_prod
  结论: a in s -> a ∣ s.prod
  证明: Quotient.inductionOn s (fun l a h => by simpa using List.dvd_prod h) a

Depends on / 依赖: List.dvd_prod, Quotient, Quotient.inductionOn, dvd_prod, inductionOn
-/
lemma dvd_prod : a in s -> a ∣ s.prod :=
  Quotient.inductionOn s (fun l a h => by simpa using List.dvd_prod h) a

/--
lemma `fst_prod` / 引理 `fst_prod`

English:
lemma fst_prod
  given: (s : Multiset (M × N))
  statement: s.prod.1 = (s.map Prod.fst).prod
  proof: map_multiset_prod (MonoidHom.fst _ _) _

中文:
引理 fst_prod
  条件: (s : Multiset (M × N))
  结论: s.prod.1 = (s.map Prod.fst).prod
  证明: map_multiset_prod (MonoidHom.fst _ _) _
-/
@[to_additive] lemma fst_prod (s : Multiset (M × N)) : s.prod.1 = (s.map Prod.fst).prod :=
  map_multiset_prod (MonoidHom.fst _ _) _

/--
lemma `snd_prod` / 引理 `snd_prod`

English:
lemma snd_prod
  given: (s : Multiset (M × N))
  statement: s.prod.2 = (s.map Prod.snd).prod
  proof: map_multiset_prod (MonoidHom.snd _ _) _

中文:
引理 snd_prod
  条件: (s : Multiset (M × N))
  结论: s.prod.2 = (s.map Prod.snd).prod
  证明: map_multiset_prod (MonoidHom.snd _ _) _
-/
@[to_additive] lemma snd_prod (s : Multiset (M × N)) : s.prod.2 = (s.map Prod.snd).prod :=
  map_multiset_prod (MonoidHom.snd _ _) _

end CommMonoid

/--
theorem `prod_dvd_prod_of_dvd` / 定理 `prod_dvd_prod_of_dvd`

English:
theorem prod_dvd_prod_of_dvd
  statement: [CommMonoid N] {S : Multiset M} (g1 g2 : M -> N)
  proof: by
  apply Multiset.induction_on' S
  · simp
  intro a T haS _ IH
  simp [mul_dvd_mul (h a haS) IH]

中文:
定理 prod_dvd_prod_of_dvd
  结论: [CommMonoid N] {S : Multiset M} (g1 g2 : M -> N)
  证明: by
  apply Multiset.induction_on' S
  · simp
  intro a T haS _ IH
  simp [mul_dvd_mul (h a haS) IH]

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on, mul_dvd_mul
-/
theorem prod_dvd_prod_of_dvd [CommMonoid N] {S : Multiset M} (g1 g2 : M -> N)
    (h : forall a in S, g1 a ∣ g2 a) : (Multiset.map g1 S).prod ∣ (Multiset.map g2 S).prod := by
  apply Multiset.induction_on' S
  · simp
  intro a T haS _ IH
  simp [mul_dvd_mul (h a haS) IH]

section AddCommMonoid

variable [AddCommMonoid M]

/--
Definition of `sumAddMonoidHom` / `sumAddMonoidHom` 的定义

English:
definition sumAddMonoidHom
  signature: : Multiset M ->+ M where
  body: sum
  map_zero' := sum_zero
  map_add' := sum_add

@[simp]

中文:
定义 sumAddMonoidHom
  签名: : Multiset M ->+ M where
  定义体: sum
  map_zero' := sum_zero
  map_add' := sum_add

@[simp]
-/
def sumAddMonoidHom : Multiset M ->+ M where
  toFun := sum
  map_zero' := sum_zero
  map_add' := sum_add

@[simp]
/--
theorem `coe_sumAddMonoidHom` / 定理 `coe_sumAddMonoidHom`

English:
theorem coe_sumAddMonoidHom
  statement: (sumAddMonoidHom : Multiset M -> M) = sum
  proof: rfl

中文:
定理 coe_sumAddMonoidHom
  结论: (sumAddMonoidHom : Multiset M -> M) = sum
  证明: rfl
-/
theorem coe_sumAddMonoidHom : (sumAddMonoidHom : Multiset M -> M) = sum :=
  rfl

end AddCommMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid G] {m : Multiset ι} {f g : ι -> G}

@[to_additive]
/--
theorem `prod_map_inv'` / 定理 `prod_map_inv'`

English:
theorem prod_map_inv'
  given: (m : Multiset G)
  statement: (m.map Inv.inv).prod = m.prod⁻¹
  proof: m.prod_hom (invMonoidHom : G ->* G)

@[to_additive (attr := simp)]

中文:
定理 prod_map_inv'
  条件: (m : Multiset G)
  结论: (m.map Inv.inv).prod = m.prod⁻¹
  证明: m.prod_hom (invMonoidHom : G ->* G)

@[to_additive (attr := simp)]

Depends on / 依赖: invMonoidHom, m.prod_hom, prod_hom
-/
theorem prod_map_inv' (m : Multiset G) : (m.map Inv.inv).prod = m.prod⁻¹ :=
  m.prod_hom (invMonoidHom : G ->* G)

@[to_additive (attr := simp)]
/--
theorem `prod_map_inv` / 定理 `prod_map_inv`

English:
theorem prod_map_inv
  statement: (m.map fun i => (f i)⁻¹).prod = (m.map f).prod⁻¹
  proof: by
  rw [← (m.map f).prod_map_inv']; rw [map_map]; rw [Function.comp_def]

@[to_additive (attr := simp)]

中文:
定理 prod_map_inv
  结论: (m.map fun i => (f i)⁻¹).prod = (m.map f).prod⁻¹
  证明: by
  rw [← (m.map f).prod_map_inv']; rw [map_map]; rw [Function.comp_def]

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, comp_def, m.map, map_map, prod_map_inv
-/
theorem prod_map_inv : (m.map fun i => (f i)⁻¹).prod = (m.map f).prod⁻¹ := by
  rw [← (m.map f).prod_map_inv']; rw [map_map]; rw [Function.comp_def]

@[to_additive (attr := simp)]
/--
theorem `prod_map_div` / 定理 `prod_map_div`

English:
theorem prod_map_div
  statement: (m.map fun i => f i / g i).prod = (m.map f).prod / (m.map g).prod
  proof: m.prod_hom₂ (· / ·) mul_div_mul_comm (div_one _) _ _

中文:
定理 prod_map_div
  结论: (m.map fun i => f i / g i).prod = (m.map f).prod / (m.map g).prod
  证明: m.prod_hom₂ (· / ·) mul_div_mul_comm (div_one _) _ _

Depends on / 依赖: div_one, m.prod_hom, mul_div_mul_comm
-/
theorem prod_map_div : (m.map fun i => f i / g i).prod = (m.map f).prod / (m.map g).prod :=
  m.prod_hom₂ (· / ·) mul_div_mul_comm (div_one _) _ _

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `prod_map_zpow` / 定理 `prod_map_zpow`

English:
theorem prod_map_zpow
  given: {n : Int}
  statement: (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n
  proof: by
  convert! (m.map f).prod_hom (zpowGroupHom n : G ->* G)
  simp only [map_map, Function.comp_apply, zpowGroupHom_apply]

中文:
定理 prod_map_zpow
  条件: {n : 整数}
  结论: (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n
  证明: by
  convert! (m.map f).prod_hom (zpowGroupHom n : G ->* G)
  simp only [map_map, Function.comp_apply, zpowGroupHom_apply]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, convert, m.map, map_map, prod_hom, zpowGroupHom, zpowGroupHom_apply
-/
theorem prod_map_zpow {n : Int} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n := by
  convert! (m.map f).prod_hom (zpowGroupHom n : G ->* G)
  simp only [map_map, Function.comp_apply, zpowGroupHom_apply]

end DivisionCommMonoid

@[simp]
/--
theorem `sum_map_singleton` / 定理 `sum_map_singleton`

English:
theorem sum_map_singleton
  given: (s : Multiset M)
  statement: (s.map fun a => ({a} : Multiset M)).sum = s
  proof: Multiset.induction_on s (by simp) (by simp)

中文:
定理 sum_map_singleton
  条件: (s : Multiset M)
  结论: (s.map fun a => ({a} : Multiset M)).sum = s
  证明: Multiset.induction_on s (by simp) (by simp)

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on
-/
theorem sum_map_singleton (s : Multiset M) : (s.map fun a => ({a} : Multiset M)).sum = s :=
  Multiset.induction_on s (by simp) (by simp)

/--
theorem `sum_nat_mod` / 定理 `sum_nat_mod`

English:
theorem sum_nat_mod
  given: (s : Multiset Nat) (n : Nat)
  statement: s.sum % n = (s.map (· % n)).sum % n
  proof: by
  induction s using Multiset.induction <;> simp [Nat.add_mod, *]

中文:
定理 sum_nat_mod
  条件: (s : Multiset 自然数) (n : 自然数)
  结论: s.sum % n = (s.map (· % n)).sum % n
  证明: by
  induction s using Multiset.induction <;> simp [Nat.add_mod, *]

Depends on / 依赖: Multiset, Multiset.induction, Nat.add_mod, add_mod
-/
theorem sum_nat_mod (s : Multiset Nat) (n : Nat) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Nat.add_mod, *]

/--
theorem `prod_nat_mod` / 定理 `prod_nat_mod`

English:
theorem prod_nat_mod
  given: (s : Multiset Nat) (n : Nat)
  statement: s.prod % n = (s.map (· % n)).prod % n
  proof: by
  induction s using Multiset.induction <;> simp [Nat.mul_mod, *]

中文:
定理 prod_nat_mod
  条件: (s : Multiset 自然数) (n : 自然数)
  结论: s.prod % n = (s.map (· % n)).prod % n
  证明: by
  induction s using Multiset.induction <;> simp [Nat.mul_mod, *]

Depends on / 依赖: Multiset, Multiset.induction, Nat.mul_mod, mul_mod
-/
theorem prod_nat_mod (s : Multiset Nat) (n : Nat) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Nat.mul_mod, *]

/--
theorem `sum_int_mod` / 定理 `sum_int_mod`

English:
theorem sum_int_mod
  given: (s : Multiset Int) (n : Int)
  statement: s.sum % n = (s.map (· % n)).sum % n
  proof: by
  induction s using Multiset.induction <;> simp [Int.add_emod, *]

中文:
定理 sum_int_mod
  条件: (s : Multiset 整数) (n : 整数)
  结论: s.sum % n = (s.map (· % n)).sum % n
  证明: by
  induction s using Multiset.induction <;> simp [Int.add_emod, *]

Depends on / 依赖: Int.add_emod, Multiset, Multiset.induction, add_emod
-/
theorem sum_int_mod (s : Multiset Int) (n : Int) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Int.add_emod, *]

/--
theorem `prod_int_mod` / 定理 `prod_int_mod`

English:
theorem prod_int_mod
  given: (s : Multiset Int) (n : Int)
  statement: s.prod % n = (s.map (· % n)).prod % n
  proof: by
  induction s using Multiset.induction <;> simp [Int.mul_emod, *]

中文:
定理 prod_int_mod
  条件: (s : Multiset 整数) (n : 整数)
  结论: s.prod % n = (s.map (· % n)).prod % n
  证明: by
  induction s using Multiset.induction <;> simp [Int.mul_emod, *]

Depends on / 依赖: Int.mul_emod, Multiset, Multiset.induction, mul_emod
-/
theorem prod_int_mod (s : Multiset Int) (n : Int) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Int.mul_emod, *]

section OrderedSub

/--
theorem `sum_map_tsub` / 定理 `sum_map_tsub`

English:
theorem sum_map_tsub
  statement: [AddCommMonoid M] [PartialOrder M] [ExistsAddOfLE M]
  proof: eq_tsub_of_add_eq by
    rw [← sum_map_add]
    congr 1
exact map_congr rfl fun x hx => tsub_add_cancel_of_le hfg _ hx

中文:
定理 sum_map_tsub
  结论: [AddCommMonoid M] [PartialOrder M] [ExistsAddOfLE M]
  证明: eq_tsub_of_add_eq by
    rw [← sum_map_add]
    congr 1
exact map_congr rfl fun x hx => tsub_add_cancel_of_le hfg _ hx

Depends on / 依赖: eq_tsub_of_add_eq, map_congr, sum_map_add, tsub_add_cancel_of_le
-/
theorem sum_map_tsub [AddCommMonoid M] [PartialOrder M] [ExistsAddOfLE M]
    [AddLeftMono M] [AddLeftReflectLE M] [Sub M]
    [OrderedSub M] (l : Multiset ι) {f g : ι -> M} (hfg : forall x in l, g x <= f x) :
    (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum :=
eq_tsub_of_add_eq by
    rw [← sum_map_add]
    congr 1
exact map_congr rfl fun x hx => tsub_add_cancel_of_le hfg _ hx

end OrderedSub

instance {M : Type*} : IsAddTorsionFree (Multiset M) :=
  ⟨fun n hn x y h => open scoped Classical in Multiset.ext' fun _ =>
(Nat.mul_right_inj hn).mp by simp only [← Multiset.count_nsmul, h]⟩

end Multiset
