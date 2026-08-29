/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Data.Multiset.OrderedMonoid
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Unique factorization and normalization

## Main definitions
* `UniqueFactorizationMonoid.normalizedFactors`: choose a multiset of prime factors that are unique
  by normalizing them.
* `UniqueFactorizationMonoid.normalizationMonoid`: choose a way of normalizing the elements of a UFM
-/

@[expose] public section

assert_not_exists Field

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace UniqueFactorizationMonoid

variable [CommMonoidWithZero α] [NormalizationMonoid α]
variable [UniqueFactorizationMonoid α]

/--
Definition of `normalizedFactors` / `normalizedFactors` 的定义

English:
definition normalizedFactors
  signature: (a : α)
  body: Multiset.map normalize factors a

中文:
定义 normalizedFactors
  签名: (a : α)
  定义体: Multiset.map normalize factors a

Depends on / 依赖: Multiset, Multiset.map, factors, normalize
-/
noncomputable def normalizedFactors (a : α) : Multiset α :=
Multiset.map normalize factors a

/-- An arbitrary choice of factors of `x : M` is exactly the (unique) normalized set of factors,
if `M` has a trivial group of units. -/
@[simp]
/--
theorem `factors_eq_normalizedFactors` / 定理 `factors_eq_normalizedFactors`

English:
theorem factors_eq_normalizedFactors
  statement: {M : Type*} [CommMonoidWithZero M]
  proof: by
  unfold normalizedFactors
  convert (Multiset.map_id (factors x)).symm with p
  exact normalize_eq p

中文:
定理 factors_eq_normalizedFactors
  结论: {M : 类型} [带零交换幺半群 M]
  证明: by
  unfold normalizedFactors
  convert (Multiset.map_id (factors x)).symm with p
  exact normalize_eq p

Depends on / 依赖: Multiset, Multiset.map_id, convert, factors, map_id, normalize_eq, normalizedFactors
-/
theorem factors_eq_normalizedFactors {M : Type*} [CommMonoidWithZero M]
    [UniqueFactorizationMonoid M] [Subsingleton Mˣ] (x : M) : factors x = normalizedFactors x := by
  unfold normalizedFactors
  convert (Multiset.map_id (factors x)).symm with p
  exact normalize_eq p

/--
theorem `prod_normalizedFactors` / 定理 `prod_normalizedFactors`

English:
theorem prod_normalizedFactors
  given: {a : α} (ane0 : a != 0)
  proof: by
  rw [normalizedFactors]; rw [factors]; rw [dif_neg ane0]
  refine Associated.trans ?_ (Classical.choose_spec (exists_prime_factors a ane0)).2
  rw [← Associates.mk_eq_mk_iff_associated]; rw [← Associates.prod_mk]; rw [← Associates.prod_mk]; rw [Multiset.map_map]
  congr 2
  ext
  rw [Function.comp_apply]; rw [Associates.mk_normalize]

中文:
定理 prod_normalizedFactors
  条件: {a : α} (ane0 : a != 0)
  证明: by
  rw [normalizedFactors]; rw [factors]; rw [dif_neg ane0]
  refine Associated.trans ?_ (Classical.choose_spec (exists_prime_factors a ane0)).2
  rw [← Associates.mk_eq_mk_iff_associated]; rw [← Associates.prod_mk]; rw [← Associates.prod_mk]; rw [Multiset.map_map]
  congr 2
  ext
  rw [Function.comp_apply]; rw [Associates.mk_normalize]

Depends on / 依赖: Associated, Associated.trans, Associates, Associates.mk_eq_mk_iff_associated, Associates.mk_normalize, Associates.prod_mk, Classical, Classical.choose_spec, Function, Function.comp_apply, Multiset, Multiset.map_map, choose_spec, comp_apply, dif_neg, exists_prime_factors, factors, map_map, mk_eq_mk_iff_associated, mk_normalize
-/
theorem prod_normalizedFactors {a : α} (ane0 : a != 0) :
    Associated (normalizedFactors a).prod a := by
  rw [normalizedFactors]; rw [factors]; rw [dif_neg ane0]
  refine Associated.trans ?_ (Classical.choose_spec (exists_prime_factors a ane0)).2
  rw [← Associates.mk_eq_mk_iff_associated]; rw [← Associates.prod_mk]; rw [← Associates.prod_mk]; rw [Multiset.map_map]
  congr 2
  ext
  rw [Function.comp_apply]; rw [Associates.mk_normalize]

/--
theorem `prod_normalizedFactors_eq` / 定理 `prod_normalizedFactors_eq`

English:
theorem prod_normalizedFactors_eq
  statement: {α} [CommMonoidWithZero α] [StrongNormalizationMonoid α]
  proof: by
  trans normalize (normalizedFactors a).prod
  · rw [normalizedFactors, ← coe_normalizeHom, ← map_multiset_prod, coe_normalizeHom,
      normalize_idem]
  · exact normalize_eq_normalize_iff.mpr (dvd_dvd_iff_associated.mpr (prod_normalizedFactors ane0))

中文:
定理 prod_normalizedFactors_eq
  结论: {α} [带零交换幺半群 α] [StrongNormalization幺半群 α]
  证明: by
  trans normalize (normalizedFactors a).prod
  · rw [normalizedFactors, ← coe_normalizeHom, ← map_multiset_prod, coe_normalizeHom,
      normalize_idem]
  · exact normalize_eq_normalize_iff.mpr (dvd_dvd_iff_associated.mpr (prod_normalizedFactors ane0))

Depends on / 依赖: coe_normalizeHom, dvd_dvd_iff_associated, dvd_dvd_iff_associated.mpr, map_multiset_prod, normalize, normalize_eq_normalize_iff, normalize_eq_normalize_iff.mpr, normalize_idem, normalizedFactors, prod_normalizedFactors
-/
theorem prod_normalizedFactors_eq {α} [CommMonoidWithZero α] [StrongNormalizationMonoid α]
    [UniqueFactorizationMonoid α] {a : α} (ane0 : a != 0) :
    (normalizedFactors a).prod = normalize a := by
  trans normalize (normalizedFactors a).prod
  · rw [normalizedFactors, ← coe_normalizeHom, ← map_multiset_prod, coe_normalizeHom,
      normalize_idem]
  · exact normalize_eq_normalize_iff.mpr (dvd_dvd_iff_associated.mpr (prod_normalizedFactors ane0))

/--
theorem `prime_of_normalized_factor` / 定理 `prime_of_normalized_factor`

English:
theorem prime_of_normalized_factor
  given: {a : α}
  statement: forall x : α, x in normalizedFactors a -> Prime x
  proof: by
  rw [normalizedFactors]; rw [factors]
  split_ifs with ane0; · simp
  intro x hx; rcases Multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩
  rw [(normalize_associated _).prime_iff]
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 y hy

中文:
定理 prime_of_normalized_factor
  条件: {a : α}
  结论: 对任意 x : α, x in normalizedFactors a -> 素 x
  证明: by
  rw [normalizedFactors]; rw [factors]
  split_ifs with ane0; · simp
  intro x hx; rcases Multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩
  rw [(normalize_associated _).prime_iff]
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 y hy

Depends on / 依赖: Classical, Classical.choose_spec, Multiset, Multiset.mem_map, UniqueFactorizationMonoid, UniqueFactorizationMonoid.exists_prime_factors, choose_spec, exists_prime_factors, factors, mem_map, normalize_associated, normalizedFactors, prime_iff, split_ifs
-/
theorem prime_of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x := by
  rw [normalizedFactors]; rw [factors]
  split_ifs with ane0; · simp
  intro x hx; rcases Multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩
  rw [(normalize_associated _).prime_iff]
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 y hy

/--
theorem `irreducible_of_normalized_factor` / 定理 `irreducible_of_normalized_factor`

English:
theorem irreducible_of_normalized_factor
  given: {a : α}
  proof: fun x h =>
  (prime_of_normalized_factor x h).irreducible

中文:
定理 irreducible_of_normalized_factor
  条件: {a : α}
  证明: fun x h =>
  (prime_of_normalized_factor x h).irreducible
-/
theorem irreducible_of_normalized_factor {a : α} :
    forall x : α, x in normalizedFactors a -> Irreducible x := fun x h =>
  (prime_of_normalized_factor x h).irreducible

/--
theorem `normalize_normalized_factor` / 定理 `normalize_normalized_factor`

English:
theorem normalize_normalized_factor
  given: {a : α}
  proof: by
  rw [normalizedFactors]; rw [factors]
  split_ifs with h; · simp
  intro x hx
  obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 hx
  apply normalize_idem

中文:
定理 normalize_normalized_factor
  条件: {a : α}
  证明: by
  rw [normalizedFactors]; rw [factors]
  split_ifs with h; · simp
  intro x hx
  obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 hx
  apply normalize_idem

Depends on / 依赖: Multiset, Multiset.mem_map, factors, mem_map, normalize_idem, normalizedFactors, split_ifs
-/
theorem normalize_normalized_factor {a : α} :
    forall x : α, x in normalizedFactors a -> normalize x = x := by
  rw [normalizedFactors]; rw [factors]
  split_ifs with h; · simp
  intro x hx
  obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 hx
  apply normalize_idem

/--
theorem `normalizedFactors_irreducible` / 定理 `normalizedFactors_irreducible`

English:
theorem normalizedFactors_irreducible
  given: {a : α} (ha : Irreducible a)
  proof: by
  obtain ⟨p, a_assoc, hp⟩ :=
    prime_factors_irreducible ha ⟨prime_of_normalized_factor, prod_normalizedFactors ha.ne_zero⟩
  have p_mem : p in normalizedFactors a := by
    rw [hp]
    exact Multiset.mem_singleton_self _
  convert! hp
  rwa [← normalize_normalized_factor p p_mem, normalize_eq_normalize_iff, dvd_dvd_iff_associated]

中文:
定理 normalizedFactors_irreducible
  条件: {a : α} (ha : 不可约 a)
  证明: by
  obtain ⟨p, a_assoc, hp⟩ :=
    prime_factors_irreducible ha ⟨prime_of_normalized_factor, prod_normalizedFactors ha.ne_zero⟩
  have p_mem : p in normalizedFactors a := by
    rw [hp]
    exact Multiset.mem_singleton_self _
  convert! hp
  rwa [← normalize_normalized_factor p p_mem, normalize_eq_normalize_iff, dvd_dvd_iff_associated]

Depends on / 依赖: Multiset, Multiset.mem_singleton_self, a_assoc, convert, dvd_dvd_iff_associated, ha.ne_zero, mem_singleton_self, ne_zero, normalize_eq_normalize_iff, normalize_normalized_factor, normalizedFactors, p_mem, prime_factors_irreducible, prime_of_normalized_factor, prod_normalizedFactors
-/
theorem normalizedFactors_irreducible {a : α} (ha : Irreducible a) :
    normalizedFactors a = {normalize a} := by
  obtain ⟨p, a_assoc, hp⟩ :=
    prime_factors_irreducible ha ⟨prime_of_normalized_factor, prod_normalizedFactors ha.ne_zero⟩
  have p_mem : p in normalizedFactors a := by
    rw [hp]
    exact Multiset.mem_singleton_self _
  convert! hp
  rwa [← normalize_normalized_factor p p_mem, normalize_eq_normalize_iff, dvd_dvd_iff_associated]

/--
theorem `normalizedFactors_eq_of_dvd` / 定理 `normalizedFactors_eq_of_dvd`

English:
theorem normalizedFactors_eq_of_dvd
  given: (a : α)
  proof: by
  intro p hp q hq hdvd
  convert!
    normalize_eq_normalize hdvd
      ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
        (prime_of_normalized_factor _ hq).irreducible hdvd) <;>
    apply (normalize_normalized_factor _ ‹_›).symm

中文:
定理 normalizedFactors_eq_of_dvd
  条件: (a : α)
  证明: by
  intro p hp q hq hdvd
  convert!
    normalize_eq_normalize hdvd
      ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
        (prime_of_normalized_factor _ hq).irreducible hdvd) <;>
    apply (normalize_normalized_factor _ ‹_›).symm

Depends on / 依赖: convert, dvd_symm, irreducible, irreducible.dvd_symm, normalize_eq_normalize, normalize_normalized_factor, prime_of_normalized_factor
-/
theorem normalizedFactors_eq_of_dvd (a : α) :
    forallᵉ (p in normalizedFactors a) (q in normalizedFactors a), p ∣ q -> p = q := by
  intro p hp q hq hdvd
  convert!
    normalize_eq_normalize hdvd
      ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
        (prime_of_normalized_factor _ hq).irreducible hdvd) <;>
    apply (normalize_normalized_factor _ ‹_›).symm

/--
theorem `exists_mem_normalizedFactors_of_dvd` / 定理 `exists_mem_normalizedFactors_of_dvd`

English:
theorem exists_mem_normalizedFactors_of_dvd
  given: {a p : α} (ha0 : a != 0) (hp : Irreducible p)
  proof: fun ⟨b, hb⟩ =>
  have hb0 : b != 0 := fun hb0 => by simp_all
  have : Multiset.Rel Associated (p ::ₘ normalizedFactors b) (normalizedFactors a) :=
    factors_unique
      (fun _ hx =>
        (Multiset.mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_normalized_factor _))
      irreducible_of_normalized_factor
      (Associated.symm <|
        calc
          Multiset.prod (normalizedFactors a) ~ᵤ a := prod_normalizedFactors ha0
          _ = p * b := hb
          _ ~ᵤ Multiset.prod (p ::ₘ normalizedFactors b) := by
            rw [Multiset.prod_cons]
            exact (prod_normalizedFactors hb0).symm.mul_left _)
  Multiset.exists_mem_of_rel_of_mem this (by simp)

中文:
定理 存在_mem_normalizedFactors_of_dvd
  条件: {a p : α} (ha0 : a != 0) (hp : 不可约 p)
  证明: fun ⟨b, hb⟩ =>
  have hb0 : b != 0 := fun hb0 => by simp_all
  have : Multiset.Rel Associated (p ::ₘ normalizedFactors b) (normalizedFactors a) :=
    factors_unique
      (fun _ hx =>
        (Multiset.mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_normalized_factor _))
      irreducible_of_normalized_factor
      (Associated.symm <|
        calc
          Multiset.prod (normalizedFactors a) ~ᵤ a := prod_normalizedFactors ha0
          _ = p * b := hb
          _ ~ᵤ Multiset.prod (p ::ₘ normalizedFactors b) := by
            rw [Multiset.prod_cons]
            exact (prod_normalizedFactors hb0).symm.mul_left _)
  Multiset.exists_mem_of_rel_of_mem this (by simp)
-/
theorem exists_mem_normalizedFactors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) :
    p ∣ a -> exists q in normalizedFactors a, p ~ᵤ q := fun ⟨b, hb⟩ =>
  have hb0 : b != 0 := fun hb0 => by simp_all
  have : Multiset.Rel Associated (p ::ₘ normalizedFactors b) (normalizedFactors a) :=
    factors_unique
      (fun _ hx =>
        (Multiset.mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_normalized_factor _))
      irreducible_of_normalized_factor
      (Associated.symm <|
        calc
          Multiset.prod (normalizedFactors a) ~ᵤ a := prod_normalizedFactors ha0
          _ = p * b := hb
          _ ~ᵤ Multiset.prod (p ::ₘ normalizedFactors b) := by
            rw [Multiset.prod_cons]
            exact (prod_normalizedFactors hb0).symm.mul_left _)
  Multiset.exists_mem_of_rel_of_mem this (by simp)

/--
theorem `exists_mem_normalizedFactors` / 定理 `exists_mem_normalizedFactors`

English:
theorem exists_mem_normalizedFactors
  given: {x : α} (hx : x != 0) (h : ¬IsUnit x)
  proof: by
  obtain ⟨p', hp', hp'x⟩ := WfDvdMonoid.exists_irreducible_factor h hx
  obtain ⟨p, hp, _⟩ := exists_mem_normalizedFactors_of_dvd hx hp' hp'x
  exact ⟨p, hp⟩

@[simp]

中文:
定理 存在_mem_normalizedFactors
  条件: {x : α} (hx : x != 0) (h : ¬是单位 x)
  证明: by
  obtain ⟨p', hp', hp'x⟩ := WfDvdMonoid.exists_irreducible_factor h hx
  obtain ⟨p, hp, _⟩ := exists_mem_normalizedFactors_of_dvd hx hp' hp'x
  exact ⟨p, hp⟩

@[simp]

Depends on / 依赖: WfDvdMonoid, WfDvdMonoid.exists_irreducible_factor, exists_irreducible_factor, exists_mem_normalizedFactors_of_dvd
-/
theorem exists_mem_normalizedFactors {x : α} (hx : x != 0) (h : ¬IsUnit x) :
    exists p, p in normalizedFactors x := by
  obtain ⟨p', hp', hp'x⟩ := WfDvdMonoid.exists_irreducible_factor h hx
  obtain ⟨p, hp, _⟩ := exists_mem_normalizedFactors_of_dvd hx hp' hp'x
  exact ⟨p, hp⟩

@[simp]
/--
theorem `normalizedFactors_zero` / 定理 `normalizedFactors_zero`

English:
theorem normalizedFactors_zero
  statement: normalizedFactors (0 : α) = 0
  proof: by
  simp [normalizedFactors, factors]

@[simp]

中文:
定理 normalizedFactors_zero
  结论: normalizedFactors (0 : α) = 0
  证明: by
  simp [normalizedFactors, factors]

@[simp]

Depends on / 依赖: factors, normalizedFactors
-/
theorem normalizedFactors_zero : normalizedFactors (0 : α) = 0 := by
  simp [normalizedFactors, factors]

@[simp]
/--
theorem `normalizedFactors_one` / 定理 `normalizedFactors_one`

English:
theorem normalizedFactors_one
  statement: normalizedFactors (1 : α) = 0
  proof: by
  rcases subsingleton_or_nontrivial α with h | h
  · dsimp [normalizedFactors, factors]
    simp [Subsingleton.elim (1 : α) 0]
  · rw [← Multiset.rel_zero_right]
    apply factors_unique irreducible_of_normalized_factor
    · intro x hx
      exfalso
      apply Multiset.notMem_zero x hx
    · apply prod_normalizedFactors one_ne_zero

@[simp]

中文:
定理 normalizedFactors_one
  结论: normalizedFactors (1 : α) = 0
  证明: by
  rcases subsingleton_or_nontrivial α with h | h
  · dsimp [normalizedFactors, factors]
    simp [Subsingleton.elim (1 : α) 0]
  · rw [← Multiset.rel_zero_right]
    apply factors_unique irreducible_of_normalized_factor
    · intro x hx
      exfalso
      apply Multiset.notMem_zero x hx
    · apply prod_normalizedFactors one_ne_zero

@[simp]

Depends on / 依赖: Multiset, Multiset.notMem_zero, Multiset.rel_zero_right, Subsingleton, Subsingleton.elim, factors, factors_unique, irreducible_of_normalized_factor, normalizedFactors, notMem_zero, one_ne_zero, prod_normalizedFactors, rel_zero_right, subsingleton_or_nontrivial
-/
theorem normalizedFactors_one : normalizedFactors (1 : α) = 0 := by
  rcases subsingleton_or_nontrivial α with h | h
  · dsimp [normalizedFactors, factors]
    simp [Subsingleton.elim (1 : α) 0]
  · rw [← Multiset.rel_zero_right]
    apply factors_unique irreducible_of_normalized_factor
    · intro x hx
      exfalso
      apply Multiset.notMem_zero x hx
    · apply prod_normalizedFactors one_ne_zero

@[simp]
/--
theorem `normalizedFactors_mul` / 定理 `normalizedFactors_mul`

English:
theorem normalizedFactors_mul
  given: {x y : α} (hx : x != 0) (hy : y != 0)
  proof: by
  have h : (normalize : α -> α) = Associates.out ∘ Associates.mk := by
    ext
    rw [Function.comp_apply]; rw [Associates.out_mk]
  rw [← Multiset.map_id' (normalizedFactors (x * y))]; rw [← Multiset.map_id' (normalizedFactors x)]; rw [←
    Multiset.map_id' (normalizedFactors y)]; rw [← Multiset.map_congr rfl normalize_normalized_factor]; rw [←
    Multiset.map_congr rfl normalize_normalized_factor]; rw [←
    Multiset.map_congr rfl normalize_normalized_factor]; rw [← Multiset.map_add]; rw [h]; rw [←
    Multiset.map_map Associates.out]; rw [eq_comm]; rw [← Multiset.map_map Associates.out]
  refine congr rfl ?_
  apply Multiset.map_mk_eq_map_mk_of_rel
  apply factors_unique
  · intro x hx
    rcases Multiset.mem_add.1 hx with (hx | hx) <;> exact irreducible_of_normalized_factor x hx
  · exact irreducible_of_normalized_factor
  · rw [Multiset.prod_add]
    exact
      ((prod_normalizedFactors hx).mul_mul (prod_normalizedFactors hy)).trans
        (prod_normalizedFactors (mul_ne_zero hx hy)).symm

@[simp]

中文:
定理 normalizedFactors_mul
  条件: {x y : α} (hx : x != 0) (hy : y != 0)
  证明: by
  have h : (normalize : α -> α) = Associates.out ∘ Associates.mk := by
    ext
    rw [Function.comp_apply]; rw [Associates.out_mk]
  rw [← Multiset.map_id' (normalizedFactors (x * y))]; rw [← Multiset.map_id' (normalizedFactors x)]; rw [←
    Multiset.map_id' (normalizedFactors y)]; rw [← Multiset.map_congr rfl normalize_normalized_factor]; rw [←
    Multiset.map_congr rfl normalize_normalized_factor]; rw [←
    Multiset.map_congr rfl normalize_normalized_factor]; rw [← Multiset.map_add]; rw [h]; rw [←
    Multiset.map_map Associates.out]; rw [eq_comm]; rw [← Multiset.map_map Associates.out]
  refine congr rfl ?_
  apply Multiset.map_mk_eq_map_mk_of_rel
  apply factors_unique
  · intro x hx
    rcases Multiset.mem_add.1 hx with (hx | hx) <;> exact irreducible_of_normalized_factor x hx
  · exact irreducible_of_normalized_factor
  · rw [Multiset.prod_add]
    exact
      ((prod_normalizedFactors hx).mul_mul (prod_normalizedFactors hy)).trans
        (prod_normalizedFactors (mul_ne_zero hx hy)).symm

@[simp]

Depends on / 依赖: Associates, Associates.mk, Associates.out, Associates.out_mk, Function, Function.comp_apply, Multiset, Multiset.map, Multiset.map_add, Multiset.map_congr, Multiset.map_id, comp_apply, map_add, map_congr, map_id, normalize, normalize_normalized_factor, normalizedFactors, out_mk
-/
theorem normalizedFactors_mul {x y : α} (hx : x != 0) (hy : y != 0) :
    normalizedFactors (x * y) = normalizedFactors x + normalizedFactors y := by
  have h : (normalize : α -> α) = Associates.out ∘ Associates.mk := by
    ext
    rw [Function.comp_apply]; rw [Associates.out_mk]
  rw [← Multiset.map_id' (normalizedFactors (x * y))]; rw [← Multiset.map_id' (normalizedFactors x)]; rw [←
    Multiset.map_id' (normalizedFactors y)]; rw [← Multiset.map_congr rfl normalize_normalized_factor]; rw [←
    Multiset.map_congr rfl normalize_normalized_factor]; rw [←
    Multiset.map_congr rfl normalize_normalized_factor]; rw [← Multiset.map_add]; rw [h]; rw [←
    Multiset.map_map Associates.out]; rw [eq_comm]; rw [← Multiset.map_map Associates.out]
  refine congr rfl ?_
  apply Multiset.map_mk_eq_map_mk_of_rel
  apply factors_unique
  · intro x hx
    rcases Multiset.mem_add.1 hx with (hx | hx) <;> exact irreducible_of_normalized_factor x hx
  · exact irreducible_of_normalized_factor
  · rw [Multiset.prod_add]
    exact
      ((prod_normalizedFactors hx).mul_mul (prod_normalizedFactors hy)).trans
        (prod_normalizedFactors (mul_ne_zero hx hy)).symm

@[simp]
/--
theorem `normalizedFactors_pow` / 定理 `normalizedFactors_pow`

English:
theorem normalizedFactors_pow
  given: {x : α} (n : Nat)
  proof: by
  induction n with
  | zero => simp [zero_nsmul]
  | succ n ih =>
    by_cases h0 : x = 0
    · simp [h0, zero_pow n.succ_ne_zero, nsmul_zero]
    rw [pow_succ']; rw [succ_nsmul']; rw [normalizedFactors_mul h0 (pow_ne_zero _ h0)]; rw [ih]

中文:
定理 normalizedFactors_pow
  条件: {x : α} (n : 自然数)
  证明: by
  induction n with
  | zero => simp [zero_nsmul]
  | succ n ih =>
    by_cases h0 : x = 0
    · simp [h0, zero_pow n.succ_ne_zero, nsmul_zero]
    rw [pow_succ']; rw [succ_nsmul']; rw [normalizedFactors_mul h0 (pow_ne_zero _ h0)]; rw [ih]

Depends on / 依赖: n.succ_ne_zero, normalizedFactors_mul, nsmul_zero, pow_ne_zero, pow_succ, succ_ne_zero, succ_nsmul, zero_nsmul, zero_pow
-/
theorem normalizedFactors_pow {x : α} (n : Nat) :
    normalizedFactors (x ^ n) = n • normalizedFactors x := by
  induction n with
  | zero => simp [zero_nsmul]
  | succ n ih =>
    by_cases h0 : x = 0
    · simp [h0, zero_pow n.succ_ne_zero, nsmul_zero]
    rw [pow_succ']; rw [succ_nsmul']; rw [normalizedFactors_mul h0 (pow_ne_zero _ h0)]; rw [ih]

/--
theorem `_root_.Irreducible.normalizedFactors_pow` / 定理 `_root_.Irreducible.normalizedFactors_pow`

English:
theorem _root_.Irreducible.normalizedFactors_pow
  given: {p : α} (hp : Irreducible p) (k : Nat)
  proof: by
  rw [UniqueFactorizationMonoid.normalizedFactors_pow]; rw [normalizedFactors_irreducible hp]; rw [Multiset.nsmul_singleton]

中文:
定理 _root_.不可约.normalizedFactors_pow
  条件: {p : α} (hp : 不可约 p) (k : 自然数)
  证明: by
  rw [UniqueFactorizationMonoid.normalizedFactors_pow]; rw [normalizedFactors_irreducible hp]; rw [Multiset.nsmul_singleton]

Depends on / 依赖: Multiset, Multiset.nsmul_singleton, UniqueFactorizationMonoid, UniqueFactorizationMonoid.normalizedFactors_pow, normalizedFactors_irreducible, normalizedFactors_pow, nsmul_singleton
-/
theorem _root_.Irreducible.normalizedFactors_pow {p : α} (hp : Irreducible p) (k : Nat) :
    normalizedFactors (p ^ k) = Multiset.replicate k (normalize p) := by
  rw [UniqueFactorizationMonoid.normalizedFactors_pow]; rw [normalizedFactors_irreducible hp]; rw [Multiset.nsmul_singleton]

/--
theorem `normalizedFactors_prod_eq` / 定理 `normalizedFactors_prod_eq`

English:
theorem normalizedFactors_prod_eq
  given: (s : Multiset α) (hs : forall a in s, Irreducible a)
  proof: by
  induction s using Multiset.induction with
  | empty => rw [Multiset.prod_zero, normalizedFactors_one, Multiset.map_zero]
  | cons a s ih =>
    have ia := hs a (Multiset.mem_cons_self a _)
    have ib := fun b h => hs b (Multiset.mem_cons_of_mem h)
    obtain rfl | ⟨b, hb⟩ := s.empty_or_exists_mem
    · rw [Multiset.cons_zero, Multiset.prod_singleton, Multiset.map_singleton,
        normalizedFactors_irreducible ia]
    have := nontrivial_of_ne b 0 (ib b hb).ne_zero
    rw [Multiset.prod_cons]; rw [Multiset.map_cons]; rw [normalizedFactors_mul ia.ne_zero (Multiset.prod_ne_zero fun h => (ib 0 h).ne_zero rfl)]; rw [normalizedFactors_irreducible ia]; rw [ih ib]; rw [Multiset.singleton_add]

中文:
定理 normalizedFactors_prod_eq
  条件: (s : Multiset α) (hs : 对任意 a in s, 不可约 a)
  证明: by
  induction s using Multiset.induction with
  | empty => rw [Multiset.prod_zero, normalizedFactors_one, Multiset.map_zero]
  | cons a s ih =>
    have ia := hs a (Multiset.mem_cons_self a _)
    have ib := fun b h => hs b (Multiset.mem_cons_of_mem h)
    obtain rfl | ⟨b, hb⟩ := s.empty_or_exists_mem
    · rw [Multiset.cons_zero, Multiset.prod_singleton, Multiset.map_singleton,
        normalizedFactors_irreducible ia]
    have := nontrivial_of_ne b 0 (ib b hb).ne_zero
    rw [Multiset.prod_cons]; rw [Multiset.map_cons]; rw [normalizedFactors_mul ia.ne_zero (Multiset.prod_ne_zero fun h => (ib 0 h).ne_zero rfl)]; rw [normalizedFactors_irreducible ia]; rw [ih ib]; rw [Multiset.singleton_add]

Depends on / 依赖: Multiset, Multiset.cons_zero, Multiset.induction, Multiset.map_cons, Multiset.map_singleton, Multiset.map_zero, Multiset.mem_cons_of_mem, Multiset.mem_cons_self, Multiset.prod_cons, Multiset.prod_singleton, Multiset.prod_zero, cons_zero, empty_or_exists_mem, map_cons, map_singleton, map_zero, mem_cons_of_mem, mem_cons_self, ne_zero, nontrivial_of_ne
-/
theorem normalizedFactors_prod_eq (s : Multiset α) (hs : forall a in s, Irreducible a) :
    normalizedFactors s.prod = s.map normalize := by
  induction s using Multiset.induction with
  | empty => rw [Multiset.prod_zero, normalizedFactors_one, Multiset.map_zero]
  | cons a s ih =>
    have ia := hs a (Multiset.mem_cons_self a _)
    have ib := fun b h => hs b (Multiset.mem_cons_of_mem h)
    obtain rfl | ⟨b, hb⟩ := s.empty_or_exists_mem
    · rw [Multiset.cons_zero, Multiset.prod_singleton, Multiset.map_singleton,
        normalizedFactors_irreducible ia]
    have := nontrivial_of_ne b 0 (ib b hb).ne_zero
    rw [Multiset.prod_cons]; rw [Multiset.map_cons]; rw [normalizedFactors_mul ia.ne_zero (Multiset.prod_ne_zero fun h => (ib 0 h).ne_zero rfl)]; rw [normalizedFactors_irreducible ia]; rw [ih ib]; rw [Multiset.singleton_add]

/--
theorem `dvd_iff_normalizedFactors_le_normalizedFactors` / 定理 `dvd_iff_normalizedFactors_le_normalizedFactors`

English:
theorem dvd_iff_normalizedFactors_le_normalizedFactors
  given: {x y : α} (hx : x != 0) (hy : y != 0)
  proof: by
  constructor
  · rintro ⟨c, rfl⟩
    simp [hx, right_ne_zero_of_mul hy]
  · rw [← (prod_normalizedFactors hx).dvd_iff_dvd_left, ←
      (prod_normalizedFactors hy).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le

中文:
定理 dvd_iff_normalizedFactors_le_normalizedFactors
  条件: {x y : α} (hx : x != 0) (hy : y != 0)
  证明: by
  constructor
  · rintro ⟨c, rfl⟩
    simp [hx, right_ne_zero_of_mul hy]
  · rw [← (prod_normalizedFactors hx).dvd_iff_dvd_left, ←
      (prod_normalizedFactors hy).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le

Depends on / 依赖: Multiset, Multiset.prod_dvd_prod_of_le, dvd_iff_dvd_left, dvd_iff_dvd_right, prod_dvd_prod_of_le, prod_normalizedFactors, right_ne_zero_of_mul
-/
theorem dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x != 0) (hy : y != 0) :
    x ∣ y ↔ normalizedFactors x <= normalizedFactors y := by
  constructor
  · rintro ⟨c, rfl⟩
    simp [hx, right_ne_zero_of_mul hy]
  · rw [← (prod_normalizedFactors hx).dvd_iff_dvd_left, ←
      (prod_normalizedFactors hy).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le

/--
theorem `_root_.Associated.normalizedFactors_eq` / 定理 `_root_.Associated.normalizedFactors_eq`

English:
theorem _root_.Associated.normalizedFactors_eq
  given: {a b : α} (h : Associated a b)
  proof: by
  unfold normalizedFactors
  have h' : normalize (α := α) = Associates.out ∘ Associates.mk := funext Associates.out_mk
  rw [h']; rw [← Multiset.map_map]; rw [← Multiset.map_map]; rw [Associates.rel_associated_iff_map_eq_map.mp (factors_rel_of_associated h)]

中文:
定理 _root_.Associated.normalizedFactors_eq
  条件: {a b : α} (h : Associated a b)
  证明: by
  unfold normalizedFactors
  have h' : normalize (α := α) = Associates.out ∘ Associates.mk := funext Associates.out_mk
  rw [h']; rw [← Multiset.map_map]; rw [← Multiset.map_map]; rw [Associates.rel_associated_iff_map_eq_map.mp (factors_rel_of_associated h)]

Depends on / 依赖: Associates, Associates.mk, Associates.out, Associates.out_mk, Associates.rel_associated_iff_map_eq_map.mp, Multiset, Multiset.map_map, factors_rel_of_associated, map_map, normalize, normalizedFactors, out_mk, rel_associated_iff_map_eq_map
-/
theorem _root_.Associated.normalizedFactors_eq {a b : α} (h : Associated a b) :
    normalizedFactors a = normalizedFactors b := by
  unfold normalizedFactors
  have h' : normalize (α := α) = Associates.out ∘ Associates.mk := funext Associates.out_mk
  rw [h']; rw [← Multiset.map_map]; rw [← Multiset.map_map]; rw [Associates.rel_associated_iff_map_eq_map.mp (factors_rel_of_associated h)]

/--
theorem `associated_iff_normalizedFactors_eq_normalizedFactors` / 定理 `associated_iff_normalizedFactors_eq_normalizedFactors`

English:
theorem associated_iff_normalizedFactors_eq_normalizedFactors
  given: {x y : α} (hx : x != 0) (hy : y != 0)
  proof: ⟨Associated.normalizedFactors_eq, fun h =>
    (prod_normalizedFactors hx).symm.trans (_root_.trans (by rw [h]) (prod_normalizedFactors hy))⟩

中文:
定理 associated_iff_normalizedFactors_eq_normalizedFactors
  条件: {x y : α} (hx : x != 0) (hy : y != 0)
  证明: ⟨Associated.normalizedFactors_eq, fun h =>
    (prod_normalizedFactors hx).symm.trans (_root_.trans (by rw [h]) (prod_normalizedFactors hy))⟩

Depends on / 依赖: Associated, Associated.normalizedFactors_eq, _root_, _root_.trans, normalizedFactors_eq, prod_normalizedFactors, symm.trans
-/
theorem associated_iff_normalizedFactors_eq_normalizedFactors {x y : α} (hx : x != 0) (hy : y != 0) :
    x ~ᵤ y ↔ normalizedFactors x = normalizedFactors y :=
  ⟨Associated.normalizedFactors_eq, fun h =>
    (prod_normalizedFactors hx).symm.trans (_root_.trans (by rw [h]) (prod_normalizedFactors hy))⟩

/--
theorem `normalizedFactors_of_irreducible_pow` / 定理 `normalizedFactors_of_irreducible_pow`

English:
theorem normalizedFactors_of_irreducible_pow
  given: {p : α} (hp : Irreducible p) (k : Nat)
  proof: by
  rw [normalizedFactors_pow]; rw [normalizedFactors_irreducible hp]; rw [Multiset.nsmul_singleton]

中文:
定理 normalizedFactors_of_irreducible_pow
  条件: {p : α} (hp : 不可约 p) (k : 自然数)
  证明: by
  rw [normalizedFactors_pow]; rw [normalizedFactors_irreducible hp]; rw [Multiset.nsmul_singleton]

Depends on / 依赖: Multiset, Multiset.nsmul_singleton, normalizedFactors_irreducible, normalizedFactors_pow, nsmul_singleton
-/
theorem normalizedFactors_of_irreducible_pow {p : α} (hp : Irreducible p) (k : Nat) :
    normalizedFactors (p ^ k) = Multiset.replicate k (normalize p) := by
  rw [normalizedFactors_pow]; rw [normalizedFactors_irreducible hp]; rw [Multiset.nsmul_singleton]

/--
theorem `zero_notMem_normalizedFactors` / 定理 `zero_notMem_normalizedFactors`

English:
theorem zero_notMem_normalizedFactors
  given: (x : α)
  statement: (0 : α) ∉ normalizedFactors x
  proof: fun h =>
  Prime.ne_zero (prime_of_normalized_factor _ h) rfl

中文:
定理 zero_notMem_normalizedFactors
  条件: (x : α)
  结论: (0 : α) ∉ normalizedFactors x
  证明: fun h =>
  Prime.ne_zero (prime_of_normalized_factor _ h) rfl
-/
theorem zero_notMem_normalizedFactors (x : α) : (0 : α) ∉ normalizedFactors x := fun h =>
  Prime.ne_zero (prime_of_normalized_factor _ h) rfl

/--
theorem `ne_zero_of_mem_normalizedFactors` / 定理 `ne_zero_of_mem_normalizedFactors`

English:
theorem ne_zero_of_mem_normalizedFactors
  given: {x a : α} (hx : x in normalizedFactors a)
  statement: x != 0
  proof: ne_of_mem_of_not_mem hx zero_notMem_normalizedFactors a

中文:
定理 ne_zero_of_mem_normalizedFactors
  条件: {x a : α} (hx : x in normalizedFactors a)
  结论: x != 0
  证明: ne_of_mem_of_not_mem hx zero_notMem_normalizedFactors a

Depends on / 依赖: ne_of_mem_of_not_mem, zero_notMem_normalizedFactors
-/
theorem ne_zero_of_mem_normalizedFactors {x a : α} (hx : x in normalizedFactors a) : x != 0 :=
ne_of_mem_of_not_mem hx zero_notMem_normalizedFactors a

/--
theorem `dvd_of_mem_normalizedFactors` / 定理 `dvd_of_mem_normalizedFactors`

English:
theorem dvd_of_mem_normalizedFactors
  given: {a p : α} (H : p in normalizedFactors a)
  statement: p ∣ a
  proof: by
  by_cases hcases : a = 0
  · rw [hcases]
    exact dvd_zero p
  · exact dvd_trans (Multiset.dvd_prod H) (Associated.dvd (prod_normalizedFactors hcases))

中文:
定理 dvd_of_mem_normalizedFactors
  条件: {a p : α} (H : p in normalizedFactors a)
  结论: p ∣ a
  证明: by
  by_cases hcases : a = 0
  · rw [hcases]
    exact dvd_zero p
  · exact dvd_trans (Multiset.dvd_prod H) (Associated.dvd (prod_normalizedFactors hcases))

Depends on / 依赖: Associated, Associated.dvd, Multiset, Multiset.dvd_prod, dvd_prod, dvd_trans, dvd_zero, hcases, prod_normalizedFactors
-/
theorem dvd_of_mem_normalizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a := by
  by_cases hcases : a = 0
  · rw [hcases]
    exact dvd_zero p
  · exact dvd_trans (Multiset.dvd_prod H) (Associated.dvd (prod_normalizedFactors hcases))
/--
theorem `mem_normalizedFactors_iff` / 定理 `mem_normalizedFactors_iff`

English:
theorem mem_normalizedFactors_iff
  given: [Subsingleton αˣ] {p x : α} (hx : x != 0)
  proof: by
  constructor
  · intro h
    exact ⟨prime_of_normalized_factor p h, dvd_of_mem_normalizedFactors h⟩
  · rintro ⟨hprime, hdvd⟩
    obtain ⟨q, hqmem, hqeq⟩ := exists_mem_normalizedFactors_of_dvd hx hprime.irreducible hdvd
    rw [associated_iff_eq] at hqeq
    exact hqeq ▸ hqmem

中文:
定理 mem_normalizedFactors_iff
  条件: [子单例 αˣ] {p x : α} (hx : x != 0)
  证明: by
  constructor
  · intro h
    exact ⟨prime_of_normalized_factor p h, dvd_of_mem_normalizedFactors h⟩
  · rintro ⟨hprime, hdvd⟩
    obtain ⟨q, hqmem, hqeq⟩ := exists_mem_normalizedFactors_of_dvd hx hprime.irreducible hdvd
    rw [associated_iff_eq] at hqeq
    exact hqeq ▸ hqmem

Depends on / 依赖: associated_iff_eq, dvd_of_mem_normalizedFactors, exists_mem_normalizedFactors_of_dvd, hprime, hprime.irreducible, irreducible, prime_of_normalized_factor
-/
theorem mem_normalizedFactors_iff [Subsingleton αˣ] {p x : α} (hx : x != 0) :
    p in normalizedFactors x ↔ Prime p ∧ p ∣ x := by
  constructor
  · intro h
    exact ⟨prime_of_normalized_factor p h, dvd_of_mem_normalizedFactors h⟩
  · rintro ⟨hprime, hdvd⟩
    obtain ⟨q, hqmem, hqeq⟩ := exists_mem_normalizedFactors_of_dvd hx hprime.irreducible hdvd
    rw [associated_iff_eq] at hqeq
    exact hqeq ▸ hqmem

/--
theorem `mem_normalizedFactors_iff'` / 定理 `mem_normalizedFactors_iff'`

English:
theorem mem_normalizedFactors_iff'
  given: {p x : α} (h : x != 0)
  proof: by
  refine ⟨fun h => ⟨irreducible_of_normalized_factor p h, normalize_normalized_factor p h,
    dvd_of_mem_normalizedFactors h⟩, fun ⟨h₁, h₂, h₃⟩ => ?_⟩
  obtain ⟨y, hy₁, hy₂⟩ := exists_mem_factors_of_dvd h h₁ h₃
  exact Multiset.mem_map.mpr ⟨y, hy₁, by
    rwa [← h₂, normalize_eq_normalize_iff_associated, Associated.comm]⟩

中文:
定理 mem_normalizedFactors_iff'
  条件: {p x : α} (h : x != 0)
  证明: by
  refine ⟨fun h => ⟨irreducible_of_normalized_factor p h, normalize_normalized_factor p h,
    dvd_of_mem_normalizedFactors h⟩, fun ⟨h₁, h₂, h₃⟩ => ?_⟩
  obtain ⟨y, hy₁, hy₂⟩ := exists_mem_factors_of_dvd h h₁ h₃
  exact Multiset.mem_map.mpr ⟨y, hy₁, by
    rwa [← h₂, normalize_eq_normalize_iff_associated, Associated.comm]⟩

Depends on / 依赖: Associated, Associated.comm, Multiset, Multiset.mem_map.mpr, dvd_of_mem_normalizedFactors, exists_mem_factors_of_dvd, irreducible_of_normalized_factor, mem_map, normalize_eq_normalize_iff_associated, normalize_normalized_factor
-/
theorem mem_normalizedFactors_iff' {p x : α} (h : x != 0) :
    p in normalizedFactors x ↔ Irreducible p ∧ normalize p = p ∧ p ∣ x := by
  refine ⟨fun h => ⟨irreducible_of_normalized_factor p h, normalize_normalized_factor p h,
    dvd_of_mem_normalizedFactors h⟩, fun ⟨h₁, h₂, h₃⟩ => ?_⟩
  obtain ⟨y, hy₁, hy₂⟩ := exists_mem_factors_of_dvd h h₁ h₃
  exact Multiset.mem_map.mpr ⟨y, hy₁, by
    rwa [← h₂, normalize_eq_normalize_iff_associated, Associated.comm]⟩

/--
theorem `disjoint_normalizedFactors` / 定理 `disjoint_normalizedFactors`

English:
theorem disjoint_normalizedFactors
  given: {a b : α} (hc : IsRelPrime a b)
  proof: by
  rw [Multiset.disjoint_left]
  intro x hxa hxb
  have x_dvd_a := dvd_of_mem_normalizedFactors hxa
  have x_dvd_b := dvd_of_mem_normalizedFactors hxb
  exact (prime_of_normalized_factor x hxa).not_isUnit (hc x_dvd_a x_dvd_b)

中文:
定理 disjoint_normalizedFactors
  条件: {a b : α} (hc : IsRelPrime a b)
  证明: by
  rw [Multiset.disjoint_left]
  intro x hxa hxb
  have x_dvd_a := dvd_of_mem_normalizedFactors hxa
  have x_dvd_b := dvd_of_mem_normalizedFactors hxb
  exact (prime_of_normalized_factor x hxa).not_isUnit (hc x_dvd_a x_dvd_b)

Depends on / 依赖: Multiset, Multiset.disjoint_left, disjoint_left, dvd_of_mem_normalizedFactors, not_isUnit, prime_of_normalized_factor, x_dvd_a, x_dvd_b
-/
theorem disjoint_normalizedFactors {a b : α} (hc : IsRelPrime a b) :
    Disjoint (normalizedFactors a) (normalizedFactors b) := by
  rw [Multiset.disjoint_left]
  intro x hxa hxb
  have x_dvd_a := dvd_of_mem_normalizedFactors hxa
  have x_dvd_b := dvd_of_mem_normalizedFactors hxb
  exact (prime_of_normalized_factor x hxa).not_isUnit (hc x_dvd_a x_dvd_b)

/--
theorem `exists_associated_prime_pow_of_unique_normalized_factor` / 定理 `exists_associated_prime_pow_of_unique_normalized_factor`

English:
theorem exists_associated_prime_pow_of_unique_normalized_factor
  statement: {p r : α}
  proof: by
  use (normalizedFactors r).card
  have := UniqueFactorizationMonoid.prod_normalizedFactors hr
  rwa [Multiset.eq_replicate_of_mem fun b => h, Multiset.prod_replicate] at this

中文:
定理 存在_associated_prime_pow_of_unique_normalized_factor
  结论: {p r : α}
  证明: by
  use (normalizedFactors r).card
  have := UniqueFactorizationMonoid.prod_normalizedFactors hr
  rwa [Multiset.eq_replicate_of_mem fun b => h, Multiset.prod_replicate] at this

Depends on / 依赖: Multiset, Multiset.eq_replicate_of_mem, Multiset.prod_replicate, UniqueFactorizationMonoid, UniqueFactorizationMonoid.prod_normalizedFactors, eq_replicate_of_mem, normalizedFactors, prod_normalizedFactors, prod_replicate
-/
theorem exists_associated_prime_pow_of_unique_normalized_factor {p r : α}
    (h : forall {m}, m in normalizedFactors r -> m = p) (hr : r != 0) : exists i : Nat, Associated (p ^ i) r := by
  use (normalizedFactors r).card
  have := UniqueFactorizationMonoid.prod_normalizedFactors hr
  rwa [Multiset.eq_replicate_of_mem fun b => h, Multiset.prod_replicate] at this

/--
theorem `normalizedFactors_prod_of_prime` / 定理 `normalizedFactors_prod_of_prime`

English:
theorem normalizedFactors_prod_of_prime
  statement: [Subsingleton αˣ] {m : Multiset α}
  proof: by
  cases subsingleton_or_nontrivial α
  · obtain rfl : m = 0 := by
      refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
      simpa [Subsingleton.elim x 0] using h x hx
    simp
  · simpa only [← Multiset.rel_eq, ← associated_eq_eq] using
      prime_factors_unique prime_of_normalized_factor h
        (prod_normalizedFactors (m.prod_ne_zero_of_prime h))

中文:
定理 normalizedFactors_prod_of_prime
  结论: [子单例 αˣ] {m : Multiset α}
  证明: by
  cases subsingleton_or_nontrivial α
  · obtain rfl : m = 0 := by
      refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
      simpa [Subsingleton.elim x 0] using h x hx
    simp
  · simpa only [← Multiset.rel_eq, ← associated_eq_eq] using
      prime_factors_unique prime_of_normalized_factor h
        (prod_normalizedFactors (m.prod_ne_zero_of_prime h))

Depends on / 依赖: Multiset, Multiset.eq_zero_of_forall_notMem, Multiset.rel_eq, Subsingleton, Subsingleton.elim, associated_eq_eq, eq_zero_of_forall_notMem, m.prod_ne_zero_of_prime, prime_factors_unique, prime_of_normalized_factor, prod_ne_zero_of_prime, prod_normalizedFactors, rel_eq, subsingleton_or_nontrivial
-/
theorem normalizedFactors_prod_of_prime [Subsingleton αˣ] {m : Multiset α}
    (h : forall p in m, Prime p) : normalizedFactors m.prod = m := by
  cases subsingleton_or_nontrivial α
  · obtain rfl : m = 0 := by
      refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
      simpa [Subsingleton.elim x 0] using h x hx
    simp
  · simpa only [← Multiset.rel_eq, ← associated_eq_eq] using
      prime_factors_unique prime_of_normalized_factor h
        (prod_normalizedFactors (m.prod_ne_zero_of_prime h))

/--
theorem `mem_normalizedFactors_eq_of_associated` / 定理 `mem_normalizedFactors_eq_of_associated`

English:
theorem mem_normalizedFactors_eq_of_associated
  statement: {a b c : α} (ha : a in normalizedFactors c)
  proof: by
  rw [← normalize_normalized_factor a ha]; rw [← normalize_normalized_factor b hb]; rw [normalize_eq_normalize_iff]
  exact Associated.dvd_dvd h

@[simp]

中文:
定理 mem_normalizedFactors_eq_of_associated
  结论: {a b c : α} (ha : a in normalizedFactors c)
  证明: by
  rw [← normalize_normalized_factor a ha]; rw [← normalize_normalized_factor b hb]; rw [normalize_eq_normalize_iff]
  exact Associated.dvd_dvd h

@[simp]

Depends on / 依赖: Associated, Associated.dvd_dvd, dvd_dvd, normalize_eq_normalize_iff, normalize_normalized_factor
-/
theorem mem_normalizedFactors_eq_of_associated {a b c : α} (ha : a in normalizedFactors c)
    (hb : b in normalizedFactors c) (h : Associated a b) : a = b := by
  rw [← normalize_normalized_factor a ha]; rw [← normalize_normalized_factor b hb]; rw [normalize_eq_normalize_iff]
  exact Associated.dvd_dvd h

@[simp]
/--
theorem `normalizedFactors_pos` / 定理 `normalizedFactors_pos`

English:
theorem normalizedFactors_pos
  given: (x : α) (hx : x != 0)
  statement: 0 < normalizedFactors x ↔ ¬IsUnit x
  proof: by
  constructor
  · intro h hx
    obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero h.ne'
    exact
      (prime_of_normalized_factor _ hp).not_isUnit
        (isUnit_of_dvd_unit (dvd_of_mem_normalizedFactors hp) hx)
  · intro h
    obtain ⟨p, hp⟩ := exists_mem_normalizedFactors hx h
    exact
      bot_lt_iff_ne_bot.mpr
        (mt Multiset.eq_zero_iff_forall_notMem.mp (not_forall.mpr ⟨p, not_not.mpr hp⟩))

中文:
定理 normalizedFactors_pos
  条件: (x : α) (hx : x != 0)
  结论: 0 < normalizedFactors x ↔ ¬是单位 x
  证明: by
  constructor
  · intro h hx
    obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero h.ne'
    exact
      (prime_of_normalized_factor _ hp).not_isUnit
        (isUnit_of_dvd_unit (dvd_of_mem_normalizedFactors hp) hx)
  · intro h
    obtain ⟨p, hp⟩ := exists_mem_normalizedFactors hx h
    exact
      bot_lt_iff_ne_bot.mpr
        (mt Multiset.eq_zero_iff_forall_notMem.mp (not_forall.mpr ⟨p, not_not.mpr hp⟩))

Depends on / 依赖: Multiset, Multiset.eq_zero_iff_forall_notMem.mp, Multiset.exists_mem_of_ne_zero, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, dvd_of_mem_normalizedFactors, eq_zero_iff_forall_notMem, exists_mem_normalizedFactors, exists_mem_of_ne_zero, h.ne, isUnit_of_dvd_unit, not_forall, not_forall.mpr, not_isUnit, not_not, not_not.mpr, prime_of_normalized_factor
-/
theorem normalizedFactors_pos (x : α) (hx : x != 0) : 0 < normalizedFactors x ↔ ¬IsUnit x := by
  constructor
  · intro h hx
    obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero h.ne'
    exact
      (prime_of_normalized_factor _ hp).not_isUnit
        (isUnit_of_dvd_unit (dvd_of_mem_normalizedFactors hp) hx)
  · intro h
    obtain ⟨p, hp⟩ := exists_mem_normalizedFactors hx h
    exact
      bot_lt_iff_ne_bot.mpr
        (mt Multiset.eq_zero_iff_forall_notMem.mp (not_forall.mpr ⟨p, not_not.mpr hp⟩))

/--
theorem `normalizedFactors_eq_zero_iff` / 定理 `normalizedFactors_eq_zero_iff`

English:
theorem normalizedFactors_eq_zero_iff
  given: {x : α} (hx : x != 0)
  proof: by
  rw [← not_iff_not]; rw [← normalizedFactors_pos _ hx]; rw [pos_iff_ne_zero]

中文:
定理 normalizedFactors_eq_zero_iff
  条件: {x : α} (hx : x != 0)
  证明: by
  rw [← not_iff_not]; rw [← normalizedFactors_pos _ hx]; rw [pos_iff_ne_zero]

Depends on / 依赖: normalizedFactors_pos, not_iff_not, pos_iff_ne_zero
-/
theorem normalizedFactors_eq_zero_iff {x : α} (hx : x != 0) :
    normalizedFactors x = 0 ↔ IsUnit x := by
  rw [← not_iff_not]; rw [← normalizedFactors_pos _ hx]; rw [pos_iff_ne_zero]

/--
theorem `normalizedFactors_of_isUnit` / 定理 `normalizedFactors_of_isUnit`

English:
theorem normalizedFactors_of_isUnit
  given: {x : α} (hx : IsUnit x)
  proof: by
  obtain rfl | hx₀ := eq_or_ne x 0
  · simp
  rwa [normalizedFactors_eq_zero_iff hx₀]

中文:
定理 normalizedFactors_of_isUnit
  条件: {x : α} (hx : 是单位 x)
  证明: by
  obtain rfl | hx₀ := eq_or_ne x 0
  · simp
  rwa [normalizedFactors_eq_zero_iff hx₀]

Depends on / 依赖: eq_or_ne, normalizedFactors_eq_zero_iff
-/
theorem normalizedFactors_of_isUnit {x : α} (hx : IsUnit x) :
    normalizedFactors x = 0 := by
  obtain rfl | hx₀ := eq_or_ne x 0
  · simp
  rwa [normalizedFactors_eq_zero_iff hx₀]

/--
theorem `dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors` / 定理 `dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors`

English:
theorem dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors
  given: {x y : α} (hx : x != 0) (hy : y != 0)
  proof: by
  constructor
  · rintro ⟨_, c, hc, rfl⟩
    simp only [hx, right_ne_zero_of_mul hy, normalizedFactors_mul, Ne, not_false_iff,
      lt_add_iff_pos_right, normalizedFactors_pos, hc]
  · intro h
    exact
      dvdNotUnit_of_dvd_of_not_dvd
        ((dvd_iff_normalizedFactors_le_normalizedFactors hx hy).mpr h.le)
        (mt (dvd_iff_normalizedFactors_le_normalizedFactors hy hx).mp h.not_ge)

中文:
定理 dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors
  条件: {x y : α} (hx : x != 0) (hy : y != 0)
  证明: by
  constructor
  · rintro ⟨_, c, hc, rfl⟩
    simp only [hx, right_ne_zero_of_mul hy, normalizedFactors_mul, Ne, not_false_iff,
      lt_add_iff_pos_right, normalizedFactors_pos, hc]
  · intro h
    exact
      dvdNotUnit_of_dvd_of_not_dvd
        ((dvd_iff_normalizedFactors_le_normalizedFactors hx hy).mpr h.le)
        (mt (dvd_iff_normalizedFactors_le_normalizedFactors hy hx).mp h.not_ge)

Depends on / 依赖: dvdNotUnit_of_dvd_of_not_dvd, dvd_iff_normalizedFactors_le_normalizedFactors, h.le, h.not_ge, lt_add_iff_pos_right, normalizedFactors_mul, normalizedFactors_pos, not_false_iff, not_ge, right_ne_zero_of_mul
-/
theorem dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors {x y : α} (hx : x != 0) (hy : y != 0) :
    DvdNotUnit x y ↔ normalizedFactors x < normalizedFactors y := by
  constructor
  · rintro ⟨_, c, hc, rfl⟩
    simp only [hx, right_ne_zero_of_mul hy, normalizedFactors_mul, Ne, not_false_iff,
      lt_add_iff_pos_right, normalizedFactors_pos, hc]
  · intro h
    exact
      dvdNotUnit_of_dvd_of_not_dvd
        ((dvd_iff_normalizedFactors_le_normalizedFactors hx hy).mpr h.le)
        (mt (dvd_iff_normalizedFactors_le_normalizedFactors hy hx).mp h.not_ge)

/--
theorem `normalizedFactors_multiset_prod` / 定理 `normalizedFactors_multiset_prod`

English:
theorem normalizedFactors_multiset_prod
  given: (s : Multiset α) (hs : 0 ∉ s)
  proof: by
  cases subsingleton_or_nontrivial α
  · obtain rfl : s = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro _
      convert! hs
    simp
  induction s using Multiset.induction with
  | empty => simp
  | cons _ _ IH =>
    rw [Multiset.prod_cons]; rw [Multiset.map_cons]; rw [Multiset.sum_cons]; rw [normalizedFactors_mul]; rw [IH]
    · exact fun h => hs (Multiset.mem_cons_of_mem h)
    · exact fun h => hs (h ▸ Multiset.mem_cons_self _ _)
    · apply Multiset.prod_ne_zero
      exact fun h => hs (Multiset.mem_cons_of_mem h)

中文:
定理 normalizedFactors_multiset_prod
  条件: (s : Multiset α) (hs : 0 ∉ s)
  证明: by
  cases subsingleton_or_nontrivial α
  · obtain rfl : s = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro _
      convert! hs
    simp
  induction s using Multiset.induction with
  | empty => simp
  | cons _ _ IH =>
    rw [Multiset.prod_cons]; rw [Multiset.map_cons]; rw [Multiset.sum_cons]; rw [normalizedFactors_mul]; rw [IH]
    · exact fun h => hs (Multiset.mem_cons_of_mem h)
    · exact fun h => hs (h ▸ Multiset.mem_cons_self _ _)
    · apply Multiset.prod_ne_zero
      exact fun h => hs (Multiset.mem_cons_of_mem h)

Depends on / 依赖: Multiset, Multiset.eq_zero_of_forall_notMem, Multiset.induction, Multiset.map_cons, Multiset.mem_cons_of_mem, Multiset.mem_cons_self, Multiset.prod_cons, Multiset.prod_ne_zero, Multiset.sum_cons, convert, eq_zero_of_forall_notMem, map_cons, mem_cons_of_mem, mem_cons_self, normalizedFactors_mul, prod_cons, prod_ne_zero, subsingleton_or_nontrivial, sum_cons
-/
theorem normalizedFactors_multiset_prod (s : Multiset α) (hs : 0 ∉ s) :
    normalizedFactors (s.prod) = (s.map normalizedFactors).sum := by
  cases subsingleton_or_nontrivial α
  · obtain rfl : s = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro _
      convert! hs
    simp
  induction s using Multiset.induction with
  | empty => simp
  | cons _ _ IH =>
    rw [Multiset.prod_cons]; rw [Multiset.map_cons]; rw [Multiset.sum_cons]; rw [normalizedFactors_mul]; rw [IH]
    · exact fun h => hs (Multiset.mem_cons_of_mem h)
    · exact fun h => hs (h ▸ Multiset.mem_cons_self _ _)
    · apply Multiset.prod_ne_zero
      exact fun h => hs (Multiset.mem_cons_of_mem h)

variable {β : Type*} [CommMonoidWithZero β] [NormalizationMonoid β]
  [UniqueFactorizationMonoid β] {F : Type*} [EquivLike F α β] [MulEquivClass F α β] {f : F}

/--
Definition of `normalizedFactorsEquiv` / `normalizedFactorsEquiv` 的定义

English:
definition normalizedFactorsEquiv
  signature: (he : forall x, normalize (f x) = f (normalize x)) (a : α)
  body: Equiv.subtypeEquiv f fun x => by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · simp [mem_normalizedFactors_iff' ha,
        mem_normalizedFactors_iff' (EmbeddingLike.map_ne_zero_iff.mpr ha), map_dvd_iff_dvd_symm,
        MulEquiv.irreducible_iff, he]

@[simp]

中文:
定义 normalizedFactorsEquiv
  签名: (he : 对任意 x, normalize (f x) = f (normalize x)) (a : α)
  定义体: Equiv.subtypeEquiv f fun x => by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · simp [mem_normalizedFactors_iff' ha,
        mem_normalizedFactors_iff' (EmbeddingLike.map_ne_zero_iff.mpr ha), map_dvd_iff_dvd_symm,
        MulEquiv.irreducible_iff, he]

@[simp]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.map_ne_zero_iff.mpr, Equiv.subtypeEquiv, MulEquiv, MulEquiv.irreducible_iff, eq_or_ne, irreducible_iff, map_dvd_iff_dvd_symm, map_ne_zero_iff, mem_normalizedFactors_iff, subtypeEquiv
-/
def normalizedFactorsEquiv (he : forall x, normalize (f x) = f (normalize x)) (a : α) :
    {x // x in normalizedFactors a} ≃ {y // y in normalizedFactors (f a)} :=
  Equiv.subtypeEquiv f fun x => by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · simp [mem_normalizedFactors_iff' ha,
        mem_normalizedFactors_iff' (EmbeddingLike.map_ne_zero_iff.mpr ha), map_dvd_iff_dvd_symm,
        MulEquiv.irreducible_iff, he]

@[simp]
/--
theorem `normalizedFactorsEquiv_apply` / 定理 `normalizedFactorsEquiv_apply`

English:
theorem normalizedFactorsEquiv_apply
  statement: (he : forall x, normalize (f x) = f (normalize x))
  proof: rfl

@[simp]

中文:
定理 normalizedFactorsEquiv_apply
  结论: (he : 对任意 x, normalize (f x) = f (normalize x))
  证明: rfl

@[simp]
-/
theorem normalizedFactorsEquiv_apply (he : forall x, normalize (f x) = f (normalize x))
    {a p : α} (hp : p in normalizedFactors a) :
    normalizedFactorsEquiv he a ⟨p, hp⟩ = f p := rfl

@[simp]
/--
theorem `normalizedFactorsEquiv_symm_apply` / 定理 `normalizedFactorsEquiv_symm_apply`

English:
theorem normalizedFactorsEquiv_symm_apply
  statement: (he : forall x, normalize (f x) = f (normalize x))
  proof: rfl

中文:
定理 normalizedFactorsEquiv_symm_apply
  结论: (he : 对任意 x, normalize (f x) = f (normalize x))
  证明: rfl
-/
theorem normalizedFactorsEquiv_symm_apply (he : forall x, normalize (f x) = f (normalize x))
    {a : α} {q : β} (hq : q in normalizedFactors (f a)) :
    (normalizedFactorsEquiv he a).symm ⟨q, hq⟩ = (MulEquivClass.toMulEquiv f).symm q := rfl

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

open Multiset Associates

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

open scoped Classical in
/-- Noncomputably defines a `StrongNormalizationMonoid` structure on a `UniqueFactorizationMonoid`.
-/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def strongNormalizationMonoid
  body: strongNormalizationMonoidOfMonoidHomRightInverse
    { toFun := fun a : Associates α =>
        if a = 0 then 0
        else
          ((normalizedFactors a).map
              (Classical.choose mk_surjective.hasRightInverse : Associates α -> α)).prod
      map_one' := by nontriviality α; simp
      map_mul' := fun x y => by
        by_cases hx : x = 0
        · simp [hx]
        by_cases hy : y = 0
        · simp [hy]
        simp [hx, hy] }
    (by
      intro x
      dsimp
      by_cases hx : x = 0
      · simp [hx]
      have h : Associates.mkMonoidHom ∘ Classical.choose mk_surjective.hasRightInverse =
          (id : Associates α -> Associates α) := by
        ext x
        rw [Function.comp_apply]; rw [mkMonoidHom_apply]; rw [Classical.choose_spec mk_surjective.hasRightInverse x]
        rfl
      rw [if_neg hx]; rw [← mkMonoidHom_apply]; rw [MonoidHom.map_multiset_prod]; rw [map_map]; rw [h]; rw [map_id]; rw [←
        associated_iff_eq]
      apply prod_normalizedFactors hx)

@[deprecated (since := "2026-07-08")]
protected alias normalizationMonoid := UniqueFactorizationMonoid.strongNormalizationMonoid

中文:
定义 noncomputable
  签名: def strongNormalizationMonoid
  定义体: strongNormalizationMonoidOfMonoidHomRightInverse
    { toFun := fun a : Associates α =>
        if a = 0 then 0
        else
          ((normalizedFactors a).map
              (Classical.choose mk_surjective.hasRightInverse : Associates α -> α)).prod
      map_one' := by nontriviality α; simp
      map_mul' := fun x y => by
        by_cases hx : x = 0
        · simp [hx]
        by_cases hy : y = 0
        · simp [hy]
        simp [hx, hy] }
    (by
      intro x
      dsimp
      by_cases hx : x = 0
      · simp [hx]
      have h : Associates.mkMonoidHom ∘ Classical.choose mk_surjective.hasRightInverse =
          (id : Associates α -> Associates α) := by
        ext x
        rw [Function.comp_apply]; rw [mkMonoidHom_apply]; rw [Classical.choose_spec mk_surjective.hasRightInverse x]
        rfl
      rw [if_neg hx]; rw [← mkMonoidHom_apply]; rw [MonoidHom.map_multiset_prod]; rw [map_map]; rw [h]; rw [map_id]; rw [←
        associated_iff_eq]
      apply prod_normalizedFactors hx)

@[deprecated (since := "2026-07-08")]
protected alias normalizationMonoid := UniqueFactorizationMonoid.strongNormalizationMonoid
-/
protected noncomputable def strongNormalizationMonoid : StrongNormalizationMonoid α :=
  strongNormalizationMonoidOfMonoidHomRightInverse
    { toFun := fun a : Associates α =>
        if a = 0 then 0
        else
          ((normalizedFactors a).map
              (Classical.choose mk_surjective.hasRightInverse : Associates α -> α)).prod
      map_one' := by nontriviality α; simp
      map_mul' := fun x y => by
        by_cases hx : x = 0
        · simp [hx]
        by_cases hy : y = 0
        · simp [hy]
        simp [hx, hy] }
    (by
      intro x
      dsimp
      by_cases hx : x = 0
      · simp [hx]
      have h : Associates.mkMonoidHom ∘ Classical.choose mk_surjective.hasRightInverse =
          (id : Associates α -> Associates α) := by
        ext x
        rw [Function.comp_apply]; rw [mkMonoidHom_apply]; rw [Classical.choose_spec mk_surjective.hasRightInverse x]
        rfl
      rw [if_neg hx]; rw [← mkMonoidHom_apply]; rw [MonoidHom.map_multiset_prod]; rw [map_map]; rw [h]; rw [map_id]; rw [←
        associated_iff_eq]
      apply prod_normalizedFactors hx)

@[deprecated (since := "2026-07-08")]
protected alias normalizationMonoid := UniqueFactorizationMonoid.strongNormalizationMonoid

instance (priority := 100) : Nonempty (StrongNormalizationMonoid α) :=
  ⟨UniqueFactorizationMonoid.strongNormalizationMonoid⟩

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

open Multiset

variable {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

/--
lemma `normalizedFactors_prod_eq_self_of_subset` / 引理 `normalizedFactors_prod_eq_self_of_subset`

English:
lemma normalizedFactors_prod_eq_self_of_subset
  statement: [Subsingleton αˣ] {a : α} {m : Multiset α}
  proof: normalizedFactors_prod_of_prime fun _ h => prime_of_normalized_factor _ (mem_of_subset hm h)

中文:
引理 normalizedFactors_prod_eq_self_of_subset
  结论: [子单例 αˣ] {a : α} {m : Multiset α}
  证明: normalizedFactors_prod_of_prime fun _ h => prime_of_normalized_factor _ (mem_of_subset hm h)

Depends on / 依赖: mem_of_subset, normalizedFactors_prod_of_prime, prime_of_normalized_factor
-/
lemma normalizedFactors_prod_eq_self_of_subset [Subsingleton αˣ] {a : α} {m : Multiset α}
    (hm : m subseteq normalizedFactors a) :
    normalizedFactors m.prod = m :=
  normalizedFactors_prod_of_prime fun _ h => prime_of_normalized_factor _ (mem_of_subset hm h)

/--
lemma `prod_ne_zero_of_subset_normalizedFactors` / 引理 `prod_ne_zero_of_subset_normalizedFactors`

English:
lemma prod_ne_zero_of_subset_normalizedFactors
  statement: [NormalizationMonoid α] [Nontrivial α] {a : α}
  proof: prod_ne_zero_of_prime _ fun _ h => prime_of_normalized_factor _ (mem_of_subset hm h)

中文:
引理 prod_ne_zero_of_subset_normalizedFactors
  结论: [Normalization幺半群 α] [非平凡 α] {a : α}
  证明: prod_ne_zero_of_prime _ fun _ h => prime_of_normalized_factor _ (mem_of_subset hm h)

Depends on / 依赖: mem_of_subset, prime_of_normalized_factor, prod_ne_zero_of_prime
-/
lemma prod_ne_zero_of_subset_normalizedFactors [NormalizationMonoid α] [Nontrivial α] {a : α}
    {m : Multiset α} (hm : m subseteq normalizedFactors a) :
    m.prod != 0 :=
  prod_ne_zero_of_prime _ fun _ h => prime_of_normalized_factor _ (mem_of_subset hm h)

variable [DecidableEq α]

/--
lemma `normalizedFactors_prod_inter_eq_inter` / 引理 `normalizedFactors_prod_inter_eq_inter`

English:
lemma normalizedFactors_prod_inter_eq_inter
  given: [Subsingleton αˣ] (a b : α)
  proof: normalizedFactors_prod_eq_self_of_subset fun _ h => (mem_inter.mp h).left

中文:
引理 normalizedFactors_prod_inter_eq_inter
  条件: [子单例 αˣ] (a b : α)
  证明: normalizedFactors_prod_eq_self_of_subset fun _ h => (mem_inter.mp h).left

Depends on / 依赖: mem_inter, mem_inter.mp, normalizedFactors_prod_eq_self_of_subset
-/
lemma normalizedFactors_prod_inter_eq_inter [Subsingleton αˣ] (a b : α) :
    normalizedFactors (normalizedFactors a inter normalizedFactors b).prod =
      normalizedFactors a inter normalizedFactors b :=
  normalizedFactors_prod_eq_self_of_subset fun _ h => (mem_inter.mp h).left

/--
lemma `prod_inter_normalizedFactors_ne_zero` / 引理 `prod_inter_normalizedFactors_ne_zero`

English:
lemma prod_inter_normalizedFactors_ne_zero
  given: [NormalizationMonoid α] [Nontrivial α] (a b : α)
  proof: prod_ne_zero_of_subset_normalizedFactors fun _ h => (mem_inter.mp h).left

中文:
引理 prod_inter_normalizedFactors_ne_zero
  条件: [Normalization幺半群 α] [非平凡 α] (a b : α)
  证明: prod_ne_zero_of_subset_normalizedFactors fun _ h => (mem_inter.mp h).left

Depends on / 依赖: mem_inter, mem_inter.mp, prod_ne_zero_of_subset_normalizedFactors
-/
lemma prod_inter_normalizedFactors_ne_zero [NormalizationMonoid α] [Nontrivial α] (a b : α) :
    (normalizedFactors a inter normalizedFactors b).prod != 0 :=
  prod_ne_zero_of_subset_normalizedFactors fun _ h => (mem_inter.mp h).left

end UniqueFactorizationMonoid
