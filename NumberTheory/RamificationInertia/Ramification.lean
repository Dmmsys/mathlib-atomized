/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Ramification index

Given `P : Ideal S` lying over `p : Ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **ramification index** `Ideal.ramificationIdx' p P` is the multiplicity of `P` in `map f p`.

## Implementation notes

Often the above theory is set up in the case where:
* `R` is the ring of integers of a number field `K`,
* `L` is a finite separable extension of `K`,
* `S` is the integral closure of `R` in `L`,
* `p` and `P` are maximal ideals,
* `P` is an ideal lying over `p`.

We will try to relax the above hypotheses as much as possible.

## Notation

In this file, `e` stands for the ramification index of `P` over `p`, leaving `p` and `P` implicit.

-/

@[expose] public section


namespace Ideal

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable (p : Ideal R) (P : Ideal S)

local notation "f" => algebraMap R S

open Module

open UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

section DecEq

/--
Definition of `ramificationIdx'` / `ramificationIdx'` 的定义

English:
definition ramificationIdx'
  signature: : Nat
  body: sSup {n | map f p <= P ^ n}

中文:
定义 ramificationIdx'
  签名: : 自然数
  定义体: sSup {n | map f p <= P ^ n}
-/
noncomputable def ramificationIdx' : Nat := sSup {n | map f p <= P ^ n}

variable {p P}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ramificationIdx'_eq_find` / 定理 `ramificationIdx'_eq_find`

English:
theorem ramificationIdx'_eq_find
  statement: [DecidablePred fun n => forall (k : Nat), map f p <= P ^ k -> k <= n]
  proof: by
  convert! Nat.sSup_def h

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_find := ramificationIdx'_eq_find

中文:
定理 ramificationIdx'_eq_find
  结论: [DecidablePred fun n => 对任意 (k : 自然数), map f p <= P ^ k -> k <= n]
  证明: by
  convert! Nat.sSup_def h

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_find := ramificationIdx'_eq_find
-/
theorem ramificationIdx'_eq_find [DecidablePred fun n => forall (k : Nat), map f p <= P ^ k -> k <= n]
    (h : exists n, forall k, map f p <= P ^ k -> k <= n) :
    ramificationIdx' p P = Nat.find h := by
  convert! Nat.sSup_def h

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_find := ramificationIdx'_eq_find

/--
theorem `ramificationIdx'_eq_zero` / 定理 `ramificationIdx'_eq_zero`

English:
theorem ramificationIdx'_eq_zero
  given: (h : forall n : Nat, exists k, map f p <= P ^ k ∧ n < k)
  proof: dif_neg (by push Not; exact h)

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_zero := ramificationIdx'_eq_zero

中文:
定理 ramificationIdx'_eq_zero
  条件: (h : 对任意 n : 自然数, 存在 k, map f p <= P ^ k ∧ n < k)
  证明: dif_neg (by push Not; exact h)

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_zero := ramificationIdx'_eq_zero
-/
theorem ramificationIdx'_eq_zero (h : forall n : Nat, exists k, map f p <= P ^ k ∧ n < k) :
    ramificationIdx' p P = 0 :=
  dif_neg (by push Not; exact h)

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_zero := ramificationIdx'_eq_zero

/--
theorem `ramificationIdx'_spec` / 定理 `ramificationIdx'_spec`

English:
theorem ramificationIdx'_spec
  given: {n : Nat} (hle : map f p <= P ^ n) (hgt : ¬map f p <= P ^ (n + 1))
  proof: by
  classical
  let Q : Nat -> Prop := fun m => forall k : Nat, map f p <= P ^ k -> k <= m
  have : Q n := by
    intro k hk
    refine le_of_not_gt fun hnk => ?_
    exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
  rw [ramificationIdx'_eq_find ⟨n]; rw [this⟩]
  refine le_antisymm (Nat.find_min' _ this) (le_of_not_gt fun h : Nat.find _ < n => ?_)
  obtain this' := Nat.find_spec ⟨n, this⟩
  exact h.not_ge (this' _ hle)

@[deprecated (since := "2026-07-01")] alias ramificationIdx_spec := ramificationIdx'_spec

中文:
定理 ramificationIdx'_spec
  条件: {n : 自然数} (hle : map f p <= P ^ n) (hgt : ¬map f p <= P ^ (n + 1))
  证明: by
  classical
  let Q : Nat -> Prop := fun m => forall k : Nat, map f p <= P ^ k -> k <= m
  have : Q n := by
    intro k hk
    refine le_of_not_gt fun hnk => ?_
    exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
  rw [ramificationIdx'_eq_find ⟨n]; rw [this⟩]
  refine le_antisymm (Nat.find_min' _ this) (le_of_not_gt fun h : Nat.find _ < n => ?_)
  obtain this' := Nat.find_spec ⟨n, this⟩
  exact h.not_ge (this' _ hle)

@[deprecated (since := "2026-07-01")] alias ramificationIdx_spec := ramificationIdx'_spec
-/
theorem ramificationIdx'_spec {n : Nat} (hle : map f p <= P ^ n) (hgt : ¬map f p <= P ^ (n + 1)) :
    ramificationIdx' p P = n := by
  classical
  let Q : Nat -> Prop := fun m => forall k : Nat, map f p <= P ^ k -> k <= m
  have : Q n := by
    intro k hk
    refine le_of_not_gt fun hnk => ?_
    exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
  rw [ramificationIdx'_eq_find ⟨n]; rw [this⟩]
  refine le_antisymm (Nat.find_min' _ this) (le_of_not_gt fun h : Nat.find _ < n => ?_)
  obtain this' := Nat.find_spec ⟨n, this⟩
  exact h.not_ge (this' _ hle)

@[deprecated (since := "2026-07-01")] alias ramificationIdx_spec := ramificationIdx'_spec

/--
theorem `ramificationIdx'_lt` / 定理 `ramificationIdx'_lt`

English:
theorem ramificationIdx'_lt
  given: {n : Nat} (hgt : ¬map f p <= P ^ n)
  statement: ramificationIdx' p P < n
  proof: by
  classical
  rcases n with - | n
  · simp at hgt
  · rw [Nat.lt_succ_iff]
    have : forall k, map f p <= P ^ k -> k <= n := by
      refine fun k hk => le_of_not_gt fun hnk => ?_
      exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
    rw [ramificationIdx'_eq_find ⟨n]; rw [this⟩]
    exact Nat.find_min' ⟨n, this⟩ this

@[deprecated (since := "2026-07-01")] alias ramificationIdx_lt := ramificationIdx'_lt

@[simp]

中文:
定理 ramificationIdx'_lt
  条件: {n : 自然数} (hgt : ¬map f p <= P ^ n)
  结论: ramificationIdx' p P < n
  证明: by
  classical
  rcases n with - | n
  · simp at hgt
  · rw [Nat.lt_succ_iff]
    have : forall k, map f p <= P ^ k -> k <= n := by
      refine fun k hk => le_of_not_gt fun hnk => ?_
      exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
    rw [ramificationIdx'_eq_find ⟨n]; rw [this⟩]
    exact Nat.find_min' ⟨n, this⟩ this

@[deprecated (since := "2026-07-01")] alias ramificationIdx_lt := ramificationIdx'_lt

@[simp]
-/
theorem ramificationIdx'_lt {n : Nat} (hgt : ¬map f p <= P ^ n) : ramificationIdx' p P < n := by
  classical
  rcases n with - | n
  · simp at hgt
  · rw [Nat.lt_succ_iff]
    have : forall k, map f p <= P ^ k -> k <= n := by
      refine fun k hk => le_of_not_gt fun hnk => ?_
      exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
    rw [ramificationIdx'_eq_find ⟨n]; rw [this⟩]
    exact Nat.find_min' ⟨n, this⟩ this

@[deprecated (since := "2026-07-01")] alias ramificationIdx_lt := ramificationIdx'_lt

@[simp]
/--
theorem `ramificationIdx'_bot` / 定理 `ramificationIdx'_bot`

English:
theorem ramificationIdx'_bot
  statement: ramificationIdx' (⊥ : Ideal R) P = 0
  proof: dif_neg not_exists.mpr fun n hn => n.lt_succ_self.not_ge (hn _ (by simp))

@[deprecated (since := "2026-07-01")] alias ramificationIdx_bot := ramificationIdx'_bot

@[simp]

中文:
定理 ramificationIdx'_bot
  结论: ramificationIdx' (⊥ : 理想 R) P = 0
  证明: dif_neg not_exists.mpr fun n hn => n.lt_succ_self.not_ge (hn _ (by simp))

@[deprecated (since := "2026-07-01")] alias ramificationIdx_bot := ramificationIdx'_bot

@[simp]
-/
theorem ramificationIdx'_bot : ramificationIdx' (⊥ : Ideal R) P = 0 :=
dif_neg not_exists.mpr fun n hn => n.lt_succ_self.not_ge (hn _ (by simp))

@[deprecated (since := "2026-07-01")] alias ramificationIdx_bot := ramificationIdx'_bot

@[simp]
/--
theorem `ramificationIdx'_of_not_le` / 定理 `ramificationIdx'_of_not_le`

English:
theorem ramificationIdx'_of_not_le
  given: (h : ¬map f p <= P)
  statement: ramificationIdx' p P = 0
  proof: ramificationIdx'_spec (by simp) (by simpa using h)

@[deprecated (since := "2026-07-01")] alias ramificationIdx_of_not_le := ramificationIdx'_of_not_le

中文:
定理 ramificationIdx'_of_not_le
  条件: (h : ¬map f p <= P)
  结论: ramificationIdx' p P = 0
  证明: ramificationIdx'_spec (by simp) (by simpa using h)

@[deprecated (since := "2026-07-01")] alias ramificationIdx_of_not_le := ramificationIdx'_of_not_le
-/
theorem ramificationIdx'_of_not_le (h : ¬map f p <= P) : ramificationIdx' p P = 0 :=
  ramificationIdx'_spec (by simp) (by simpa using h)

@[deprecated (since := "2026-07-01")] alias ramificationIdx_of_not_le := ramificationIdx'_of_not_le

/--
theorem `ramificationIdx'_bot'` / 定理 `ramificationIdx'_bot'`

English:
theorem ramificationIdx'_bot'
  given: (hp : p != ⊥) (hf : Function.Injective f)
  proof: ramificationIdx'_of_not_le le_bot_iff.not.mpr (map_eq_bot_iff_of_injective hf).not.mpr hp

@[deprecated (since := "2026-07-01")] alias ramificationIdx_bot' := ramificationIdx'_bot'

中文:
定理 ramificationIdx'_bot'
  条件: (hp : p != ⊥) (hf : 函数.单射 f)
  证明: ramificationIdx'_of_not_le le_bot_iff.not.mpr (map_eq_bot_iff_of_injective hf).not.mpr hp

@[deprecated (since := "2026-07-01")] alias ramificationIdx_bot' := ramificationIdx'_bot'
-/
theorem ramificationIdx'_bot' (hp : p != ⊥) (hf : Function.Injective f) :
    ramificationIdx' p (⊥ : Ideal S) = 0 :=
ramificationIdx'_of_not_le le_bot_iff.not.mpr (map_eq_bot_iff_of_injective hf).not.mpr hp

@[deprecated (since := "2026-07-01")] alias ramificationIdx_bot' := ramificationIdx'_bot'

/--
theorem `ramificationIdx'_ne_zero` / 定理 `ramificationIdx'_ne_zero`

English:
theorem ramificationIdx'_ne_zero
  statement: {e : Nat} (he : e != 0) (hle : map f p <= P ^ e)
  proof: by
  rwa [ramificationIdx'_spec hle hnle]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_zero := ramificationIdx'_ne_zero

中文:
定理 ramificationIdx'_ne_zero
  结论: {e : 自然数} (he : e != 0) (hle : map f p <= P ^ e)
  证明: by
  rwa [ramificationIdx'_spec hle hnle]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_zero := ramificationIdx'_ne_zero
-/
theorem ramificationIdx'_ne_zero {e : Nat} (he : e != 0) (hle : map f p <= P ^ e)
    (hnle : ¬map f p <= P ^ (e + 1)) : ramificationIdx' p P != 0 := by
  rwa [ramificationIdx'_spec hle hnle]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_zero := ramificationIdx'_ne_zero

/--
theorem `le_pow_of_le_ramificationIdx'` / 定理 `le_pow_of_le_ramificationIdx'`

English:
theorem le_pow_of_le_ramificationIdx'
  given: {n : Nat} (hn : n <= ramificationIdx' p P)
  proof: by
  contrapose! hn
  exact ramificationIdx'_lt hn

@[deprecated (since := "2026-07-01")] alias le_pow_of_le_ramificationIdx :=
  le_pow_of_le_ramificationIdx'

中文:
定理 le_pow_of_le_ramificationIdx'
  条件: {n : 自然数} (hn : n <= ramificationIdx' p P)
  证明: by
  contrapose! hn
  exact ramificationIdx'_lt hn

@[deprecated (since := "2026-07-01")] alias le_pow_of_le_ramificationIdx :=
  le_pow_of_le_ramificationIdx'

Depends on / 依赖: contrapose, ramificationIdx
-/
theorem le_pow_of_le_ramificationIdx' {n : Nat} (hn : n <= ramificationIdx' p P) :
    map f p <= P ^ n := by
  contrapose! hn
  exact ramificationIdx'_lt hn

@[deprecated (since := "2026-07-01")] alias le_pow_of_le_ramificationIdx :=
  le_pow_of_le_ramificationIdx'

/--
theorem `le_pow_ramificationIdx'` / 定理 `le_pow_ramificationIdx'`

English:
theorem le_pow_ramificationIdx'
  statement: map f p <= P ^ ramificationIdx' p P
  proof: le_pow_of_le_ramificationIdx' (le_refl _)

@[deprecated (since := "2026-07-01")] alias le_pow_ramificationIdx := le_pow_ramificationIdx'

中文:
定理 le_pow_ramificationIdx'
  结论: map f p <= P ^ ramificationIdx' p P
  证明: le_pow_of_le_ramificationIdx' (le_refl _)

@[deprecated (since := "2026-07-01")] alias le_pow_ramificationIdx := le_pow_ramificationIdx'

Depends on / 依赖: le_pow_of_le_ramificationIdx, le_refl
-/
theorem le_pow_ramificationIdx' : map f p <= P ^ ramificationIdx' p P :=
  le_pow_of_le_ramificationIdx' (le_refl _)

@[deprecated (since := "2026-07-01")] alias le_pow_ramificationIdx := le_pow_ramificationIdx'

/--
theorem `le_comap_pow_ramificationIdx'` / 定理 `le_comap_pow_ramificationIdx'`

English:
theorem le_comap_pow_ramificationIdx'
  statement: p <= comap f (P ^ ramificationIdx' p P)
  proof: map_le_iff_le_comap.mp le_pow_ramificationIdx'

@[deprecated (since := "2026-07-01")] alias le_comap_pow_ramificationIdx :=
  le_comap_pow_ramificationIdx'

中文:
定理 le_comap_pow_ramificationIdx'
  结论: p <= comap f (P ^ ramificationIdx' p P)
  证明: map_le_iff_le_comap.mp le_pow_ramificationIdx'

@[deprecated (since := "2026-07-01")] alias le_comap_pow_ramificationIdx :=
  le_comap_pow_ramificationIdx'

Depends on / 依赖: le_pow_ramificationIdx, map_le_iff_le_comap, map_le_iff_le_comap.mp
-/
theorem le_comap_pow_ramificationIdx' : p <= comap f (P ^ ramificationIdx' p P) :=
  map_le_iff_le_comap.mp le_pow_ramificationIdx'

@[deprecated (since := "2026-07-01")] alias le_comap_pow_ramificationIdx :=
  le_comap_pow_ramificationIdx'

/--
theorem `le_comap_of_ramificationIdx'_ne_zero` / 定理 `le_comap_of_ramificationIdx'_ne_zero`

English:
theorem le_comap_of_ramificationIdx'_ne_zero
  given: (h : ramificationIdx' p P != 0)
  statement: p <= comap f P
  proof: Ideal.map_le_iff_le_comap.mp le_pow_ramificationIdx'.trans Ideal.pow_le_self h

@[deprecated (since := "2026-07-01")] alias le_comap_of_ramificationIdx_ne_zero :=
  le_comap_of_ramificationIdx'_ne_zero

中文:
定理 le_comap_of_ramificationIdx'_ne_zero
  条件: (h : ramificationIdx' p P != 0)
  结论: p <= comap f P
  证明: Ideal.map_le_iff_le_comap.mp le_pow_ramificationIdx'.trans Ideal.pow_le_self h

@[deprecated (since := "2026-07-01")] alias le_comap_of_ramificationIdx_ne_zero :=
  le_comap_of_ramificationIdx'_ne_zero

Depends on / 依赖: Ideal.map_le_iff_le_comap.mp, Ideal.pow_le_self, le_pow_ramificationIdx, map_le_iff_le_comap, pow_le_self
-/
theorem le_comap_of_ramificationIdx'_ne_zero (h : ramificationIdx' p P != 0) : p <= comap f P :=
Ideal.map_le_iff_le_comap.mp le_pow_ramificationIdx'.trans Ideal.pow_le_self h

@[deprecated (since := "2026-07-01")] alias le_comap_of_ramificationIdx_ne_zero :=
  le_comap_of_ramificationIdx'_ne_zero

variable {S₁ : Type*} [CommRing S₁] [Algebra R S₁]

variable (p) in
/--
lemma `ramificationIdx'_comap_eq` / 引理 `ramificationIdx'_comap_eq`

English:
lemma ramificationIdx'_comap_eq
  given: (e : S ≃ₐ[R] S₁) (P : Ideal S₁)
  proof: by
  dsimp only [ramificationIdx']
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, Ideal.map_le_iff_le_comap]
  rw [← comap_coe e]; rw [← e.toRingEquiv_toRingHom]; rw [comap_coe]; rw [← RingEquiv.symm_symm (e : S ≃+* S₁)]; rw [← map_comap_of_equiv]; rw [← Ideal.map_pow]; rw [map_comap_of_equiv]; rw [← comap_coe (RingEquiv.symm _)]; rw [comap_comap]; rw [RingEquiv.symm_symm]; rw [e.toRingEquiv_toRingHom]; rw [← e.toAlgHom_toRingHom]; rw [AlgHom.comp_algebraMap]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_comap_eq := ramificationIdx'_comap_eq

中文:
引理 ramificationIdx'_comap_eq
  条件: (e : S ≃ₐ[R] S₁) (P : 理想 S₁)
  证明: by
  dsimp only [ramificationIdx']
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, Ideal.map_le_iff_le_comap]
  rw [← comap_coe e]; rw [← e.toRingEquiv_toRingHom]; rw [comap_coe]; rw [← RingEquiv.symm_symm (e : S ≃+* S₁)]; rw [← map_comap_of_equiv]; rw [← Ideal.map_pow]; rw [map_comap_of_equiv]; rw [← comap_coe (RingEquiv.symm _)]; rw [comap_comap]; rw [RingEquiv.symm_symm]; rw [e.toRingEquiv_toRingHom]; rw [← e.toAlgHom_toRingHom]; rw [AlgHom.comp_algebraMap]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_comap_eq := ramificationIdx'_comap_eq
-/
lemma ramificationIdx'_comap_eq (e : S ≃ₐ[R] S₁) (P : Ideal S₁) :
    ramificationIdx' p (P.comap e) = ramificationIdx' p P := by
  dsimp only [ramificationIdx']
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, Ideal.map_le_iff_le_comap]
  rw [← comap_coe e]; rw [← e.toRingEquiv_toRingHom]; rw [comap_coe]; rw [← RingEquiv.symm_symm (e : S ≃+* S₁)]; rw [← map_comap_of_equiv]; rw [← Ideal.map_pow]; rw [map_comap_of_equiv]; rw [← comap_coe (RingEquiv.symm _)]; rw [comap_comap]; rw [RingEquiv.symm_symm]; rw [e.toRingEquiv_toRingHom]; rw [← e.toAlgHom_toRingHom]; rw [AlgHom.comp_algebraMap]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_comap_eq := ramificationIdx'_comap_eq

variable (p) in
/--
lemma `ramificationIdx'_map_eq` / 引理 `ramificationIdx'_map_eq`

English:
lemma ramificationIdx'_map_eq
  statement: {E : Type*} [EquivLike E S S₁] [AlgEquivClass E R S S₁]
  proof: by
  rw [show P.map e = _ from P.map_comap_of_equiv (RingEquivClass.toRingEquiv e : S ≃+* S₁)]
  exact p.ramificationIdx'_comap_eq (AlgEquivClass.toAlgEquiv e).symm P

@[deprecated (since := "2026-07-01")] alias ramificationIdx_map_eq := ramificationIdx'_map_eq

中文:
引理 ramificationIdx'_map_eq
  结论: {E : 类型} [等价状 E S S₁] [代数等价类 E R S S₁]
  证明: by
  rw [show P.map e = _ from P.map_comap_of_equiv (RingEquivClass.toRingEquiv e : S ≃+* S₁)]
  exact p.ramificationIdx'_comap_eq (AlgEquivClass.toAlgEquiv e).symm P

@[deprecated (since := "2026-07-01")] alias ramificationIdx_map_eq := ramificationIdx'_map_eq
-/
lemma ramificationIdx'_map_eq {E : Type*} [EquivLike E S S₁] [AlgEquivClass E R S S₁]
    (P : Ideal S) (e : E) :
    ramificationIdx' p (P.map e) = ramificationIdx' p P := by
  rw [show P.map e = _ from P.map_comap_of_equiv (RingEquivClass.toRingEquiv e : S ≃+* S₁)]
  exact p.ramificationIdx'_comap_eq (AlgEquivClass.toAlgEquiv e).symm P

@[deprecated (since := "2026-07-01")] alias ramificationIdx_map_eq := ramificationIdx'_map_eq

/--
lemma `ramificationIdx'_ne_one_iff` / 引理 `ramificationIdx'_ne_one_iff`

English:
lemma ramificationIdx'_ne_one_iff
  given: (hp : map f p <= P)
  proof: by
  classical
  by_cases! H : forall n : Nat, exists k, p.map f <= P ^ k ∧ n < k
  · obtain ⟨k, hk, h2k⟩ := H 2
    simp [Ideal.ramificationIdx'_eq_zero H, hk.trans (Ideal.pow_le_pow_right h2k.le)]
  rw [Ideal.ramificationIdx'_eq_find H]
  constructor
  · intro he
    have : 1 <= Nat.find H := Nat.find_spec H 1 (by simpa)
    have := Nat.find_min H (m := 1) (by lia)
    push Not at this
    obtain ⟨k, hk, h1k⟩ := this
    exact hk.trans (Ideal.pow_le_pow_right (Nat.succ_le_iff.mpr h1k))
  · intro he
    have := Nat.find_spec H 2 he
    lia

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_one_iff :=
  ramificationIdx'_ne_one_iff

中文:
引理 ramificationIdx'_ne_one_iff
  条件: (hp : map f p <= P)
  证明: by
  classical
  by_cases! H : forall n : Nat, exists k, p.map f <= P ^ k ∧ n < k
  · obtain ⟨k, hk, h2k⟩ := H 2
    simp [Ideal.ramificationIdx'_eq_zero H, hk.trans (Ideal.pow_le_pow_right h2k.le)]
  rw [Ideal.ramificationIdx'_eq_find H]
  constructor
  · intro he
    have : 1 <= Nat.find H := Nat.find_spec H 1 (by simpa)
    have := Nat.find_min H (m := 1) (by lia)
    push Not at this
    obtain ⟨k, hk, h1k⟩ := this
    exact hk.trans (Ideal.pow_le_pow_right (Nat.succ_le_iff.mpr h1k))
  · intro he
    have := Nat.find_spec H 2 he
    lia

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_one_iff :=
  ramificationIdx'_ne_one_iff
-/
lemma ramificationIdx'_ne_one_iff (hp : map f p <= P) :
    ramificationIdx' p P != 1 ↔ p.map f <= P ^ 2 := by
  classical
  by_cases! H : forall n : Nat, exists k, p.map f <= P ^ k ∧ n < k
  · obtain ⟨k, hk, h2k⟩ := H 2
    simp [Ideal.ramificationIdx'_eq_zero H, hk.trans (Ideal.pow_le_pow_right h2k.le)]
  rw [Ideal.ramificationIdx'_eq_find H]
  constructor
  · intro he
    have : 1 <= Nat.find H := Nat.find_spec H 1 (by simpa)
    have := Nat.find_min H (m := 1) (by lia)
    push Not at this
    obtain ⟨k, hk, h1k⟩ := this
    exact hk.trans (Ideal.pow_le_pow_right (Nat.succ_le_iff.mpr h1k))
  · intro he
    have := Nat.find_spec H 2 he
    lia

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_one_iff :=
  ramificationIdx'_ne_one_iff

open IsLocalRing in
/--
lemma `ramificationIdx'_eq_one_of_map_localization` / 引理 `ramificationIdx'_eq_one_of_map_localization`

English:
lemma ramificationIdx'_eq_one_of_map_localization
  proof: by
  rw [← not_ne_iff (b := 1)]; rw [Ideal.ramificationIdx'_ne_one_iff hpP]
  intro h₂
  replace h₂ := Ideal.map_mono («f» := algebraMap S (Localization.AtPrime P)) h₂
  rw [Ideal.map_pow]; rw [Localization.AtPrime.map_eq_maximalIdeal]; rw [Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [H]; rw [pow_two] at h₂
  have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _) h₂
    (maximalIdeal_le_jacobson _)
  rw [← Localization.AtPrime.map_eq_maximalIdeal]; rw [Ideal.map_eq_bot_iff_of_injective] at this
  · exact hp this
  · exact IsLocalization.injective _ hp'

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_one_of_map_localization :=
  ramificationIdx'_eq_one_of_map_localization

中文:
引理 ramificationIdx'_eq_one_of_map_localization
  证明: by
  rw [← not_ne_iff (b := 1)]; rw [Ideal.ramificationIdx'_ne_one_iff hpP]
  intro h₂
  replace h₂ := Ideal.map_mono («f» := algebraMap S (Localization.AtPrime P)) h₂
  rw [Ideal.map_pow]; rw [Localization.AtPrime.map_eq_maximalIdeal]; rw [Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [H]; rw [pow_two] at h₂
  have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _) h₂
    (maximalIdeal_le_jacobson _)
  rw [← Localization.AtPrime.map_eq_maximalIdeal]; rw [Ideal.map_eq_bot_iff_of_injective] at this
  · exact hp this
  · exact IsLocalization.injective _ hp'

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_one_of_map_localization :=
  ramificationIdx'_eq_one_of_map_localization
-/
lemma ramificationIdx'_eq_one_of_map_localization
    {p : Ideal R} {P : Ideal S} [P.IsPrime] [IsNoetherianRing S]
    (hpP : map (algebraMap R S) p <= P) (hp : P != ⊥) (hp' : P.primeCompl <= nonZeroDivisors S)
    (H : p.map (algebraMap R (Localization.AtPrime P)) = maximalIdeal (Localization.AtPrime P)) :
    ramificationIdx' p P = 1 := by
  rw [← not_ne_iff (b := 1)]; rw [Ideal.ramificationIdx'_ne_one_iff hpP]
  intro h₂
  replace h₂ := Ideal.map_mono («f» := algebraMap S (Localization.AtPrime P)) h₂
  rw [Ideal.map_pow]; rw [Localization.AtPrime.map_eq_maximalIdeal]; rw [Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [H]; rw [pow_two] at h₂
  have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _) h₂
    (maximalIdeal_le_jacobson _)
  rw [← Localization.AtPrime.map_eq_maximalIdeal]; rw [Ideal.map_eq_bot_iff_of_injective] at this
  · exact hp this
  · exact IsLocalization.injective _ hp'

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_one_of_map_localization :=
  ramificationIdx'_eq_one_of_map_localization

/--
theorem `ramificationIdx'_map_self_eq_one` / 定理 `ramificationIdx'_map_self_eq_one`

English:
theorem ramificationIdx'_map_self_eq_one
  statement: [IsDedekindDomain S]
  proof: by
  refine ramificationIdx'_spec (by simp) fun h => ?_
  have : map f p ^ 1 = (map f p) ^ 2 := by
    rw [pow_one]
exact le_antisymm h pow_le_self two_ne_zero
  have := IsMulTorsionFree.pow_right_injective₀ (by rwa [one_eq_top]) h₂ this
  simp_all

@[deprecated (since := "2026-07-01")] alias ramificationIdx_map_self_eq_one :=
  ramificationIdx'_map_self_eq_one

中文:
定理 ramificationIdx'_map_self_eq_one
  结论: [是Dedekind整环 S]
  证明: by
  refine ramificationIdx'_spec (by simp) fun h => ?_
  have : map f p ^ 1 = (map f p) ^ 2 := by
    rw [pow_one]
exact le_antisymm h pow_le_self two_ne_zero
  have := IsMulTorsionFree.pow_right_injective₀ (by rwa [one_eq_top]) h₂ this
  simp_all

@[deprecated (since := "2026-07-01")] alias ramificationIdx_map_self_eq_one :=
  ramificationIdx'_map_self_eq_one
-/
theorem ramificationIdx'_map_self_eq_one [IsDedekindDomain S]
    (h₁ : map f p != ⊤) (h₂ : map f p != ⊥) : ramificationIdx' p (map f p) = 1 := by
  refine ramificationIdx'_spec (by simp) fun h => ?_
  have : map f p ^ 1 = (map f p) ^ 2 := by
    rw [pow_one]
exact le_antisymm h pow_le_self two_ne_zero
  have := IsMulTorsionFree.pow_right_injective₀ (by rwa [one_eq_top]) h₂ this
  simp_all

@[deprecated (since := "2026-07-01")] alias ramificationIdx_map_self_eq_one :=
  ramificationIdx'_map_self_eq_one

variable (p P) in
/--
theorem `ramificationIdx'_le_ramificationIdx'` / 定理 `ramificationIdx'_le_ramificationIdx'`

English:
theorem ramificationIdx'_le_ramificationIdx'
  statement: {T : Type*} [CommRing T] [Algebra R T]
  proof: by
  simp_rw [ramificationIdx', Ne] at *
  refine csSup_le_csSup' (h.imp_symm Nat.sSup_of_not_bddAbove) fun n hn => ?_
  simp_rw [hp, IsScalarTower.algebraMap_eq R S T, ← map_map, map_le_iff_le_comap]
exact comap_mono by rwa [← map_le_iff_le_comap]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_le_ramificationIdx :=
  ramificationIdx'_le_ramificationIdx'

中文:
定理 ramificationIdx'_le_ramificationIdx'
  结论: {T : 类型} [交换环 T] [代数 R T]
  证明: by
  simp_rw [ramificationIdx', Ne] at *
  refine csSup_le_csSup' (h.imp_symm Nat.sSup_of_not_bddAbove) fun n hn => ?_
  simp_rw [hp, IsScalarTower.algebraMap_eq R S T, ← map_map, map_le_iff_le_comap]
exact comap_mono by rwa [← map_le_iff_le_comap]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_le_ramificationIdx :=
  ramificationIdx'_le_ramificationIdx'
-/
theorem ramificationIdx'_le_ramificationIdx' {T : Type*} [CommRing T] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] (Q : Ideal T) (hp : p = comap f P)
    (h : ramificationIdx' p Q != 0) : ramificationIdx' P Q <= ramificationIdx' p Q := by
  simp_rw [ramificationIdx', Ne] at *
  refine csSup_le_csSup' (h.imp_symm Nat.sSup_of_not_bddAbove) fun n hn => ?_
  simp_rw [hp, IsScalarTower.algebraMap_eq R S T, ← map_map, map_le_iff_le_comap]
exact comap_mono by rwa [← map_le_iff_le_comap]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_le_ramificationIdx :=
  ramificationIdx'_le_ramificationIdx'

namespace IsDedekindDomain

variable [IsDedekindDomain S]

/--
theorem `ramificationIdx'_eq_normalizedFactors_count` / 定理 `ramificationIdx'_eq_normalizedFactors_count`

English:
theorem ramificationIdx'_eq_normalizedFactors_count
  proof: by
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  refine ramificationIdx'_spec (Ideal.le_of_dvd ?_) (mt Ideal.dvd_iff_le.mpr ?_) <;>
    rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hp0]; rw [normalizedFactors_pow]; rw [normalizedFactors_irreducible hPirr]; rw [normalize_eq]; rw [Multiset.nsmul_singleton]; rw [← Multiset.le_count_iff_replicate_le]
  exact (Nat.lt_succ_self _).not_ge

中文:
定理 ramificationIdx'_eq_normalizedFactors_count
  证明: by
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  refine ramificationIdx'_spec (Ideal.le_of_dvd ?_) (mt Ideal.dvd_iff_le.mpr ?_) <;>
    rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hp0]; rw [normalizedFactors_pow]; rw [normalizedFactors_irreducible hPirr]; rw [normalize_eq]; rw [Multiset.nsmul_singleton]; rw [← Multiset.le_count_iff_replicate_le]
  exact (Nat.lt_succ_self _).not_ge

Depends on / 依赖: Ideal.dvd_iff_le.mpr, Ideal.le_of_dvd, Ideal.prime_of_isPrime, Multiset, Multiset.le_count_iff_replicate_le, Multiset.nsmul_singleton, Nat.lt_succ_self, _spec, dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors, irreducible, le_count_iff_replicate_le, le_of_dvd, lt_succ_self, normalize_eq, normalizedFactors_irreducible, normalizedFactors_pow, not_ge, nsmul_singleton, pow_ne_zero
-/
theorem ramificationIdx'_eq_normalizedFactors_count
    (hp0 : map f p != ⊥) (hP : P.IsPrime)
    (hP0 : P != ⊥) : ramificationIdx' p P = (normalizedFactors (map f p)).count P := by
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  refine ramificationIdx'_spec (Ideal.le_of_dvd ?_) (mt Ideal.dvd_iff_le.mpr ?_) <;>
    rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hp0]; rw [normalizedFactors_pow]; rw [normalizedFactors_irreducible hPirr]; rw [normalize_eq]; rw [Multiset.nsmul_singleton]; rw [← Multiset.le_count_iff_replicate_le]
  exact (Nat.lt_succ_self _).not_ge

/--
theorem `ramificationIdx'_eq_multiplicity` / 定理 `ramificationIdx'_eq_multiplicity`

English:
theorem ramificationIdx'_eq_multiplicity
  given: (hp : map f p != ⊥) (hP : P.IsPrime)
  proof: by
  by_cases hP₂ : P = ⊥
  · rw [hP₂, ← Ideal.zero_eq_bot, multiplicity_zero_eq_zero_of_ne_zero _ hp]
    exact Ideal.ramificationIdx'_of_not_le (mt le_bot_iff.mp hp)
  rw [multiplicity_eq_of_emultiplicity_eq_some]
  rw [ramificationIdx'_eq_normalizedFactors_count hp hP hP₂]; rw [← normalize_eq P]; rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors _ hp]; rw [normalize_eq]
exact irreducible_iff_prime.mpr prime_of_isPrime hP₂ hP

中文:
定理 ramificationIdx'_eq_multiplicity
  条件: (hp : map f p != ⊥) (hP : P.是素)
  证明: by
  by_cases hP₂ : P = ⊥
  · rw [hP₂, ← Ideal.zero_eq_bot, multiplicity_zero_eq_zero_of_ne_zero _ hp]
    exact Ideal.ramificationIdx'_of_not_le (mt le_bot_iff.mp hp)
  rw [multiplicity_eq_of_emultiplicity_eq_some]
  rw [ramificationIdx'_eq_normalizedFactors_count hp hP hP₂]; rw [← normalize_eq P]; rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors _ hp]; rw [normalize_eq]
exact irreducible_iff_prime.mpr prime_of_isPrime hP₂ hP
-/
theorem ramificationIdx'_eq_multiplicity (hp : map f p != ⊥) (hP : P.IsPrime) :
    ramificationIdx' p P = multiplicity P (Ideal.map f p) := by
  by_cases hP₂ : P = ⊥
  · rw [hP₂, ← Ideal.zero_eq_bot, multiplicity_zero_eq_zero_of_ne_zero _ hp]
    exact Ideal.ramificationIdx'_of_not_le (mt le_bot_iff.mp hp)
  rw [multiplicity_eq_of_emultiplicity_eq_some]
  rw [ramificationIdx'_eq_normalizedFactors_count hp hP hP₂]; rw [← normalize_eq P]; rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors _ hp]; rw [normalize_eq]
exact irreducible_iff_prime.mpr prime_of_isPrime hP₂ hP

/--
theorem `ramificationIdx'_eq_factors_count` / 定理 `ramificationIdx'_eq_factors_count`

English:
theorem ramificationIdx'_eq_factors_count
  proof: by
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0]; rw [factors_eq_normalizedFactors]

中文:
定理 ramificationIdx'_eq_factors_count
  证明: by
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0]; rw [factors_eq_normalizedFactors]
-/
theorem ramificationIdx'_eq_factors_count
    (hp0 : map f p != ⊥) (hP : P.IsPrime) (hP0 : P != ⊥) :
    ramificationIdx' p P = (factors (map f p)).count P := by
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0]; rw [factors_eq_normalizedFactors]

/--
theorem `ramificationIdx'_ne_zero` / 定理 `ramificationIdx'_ne_zero`

English:
theorem ramificationIdx'_ne_zero
  given: (hp0 : map f p != ⊥) (hP : P.IsPrime) (le : map f p <= P)
  proof: by
  have hP0 : P != ⊥ := by
    rintro rfl
    exact hp0 (le_bot_iff.mp le)
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0]
  obtain ⟨P', hP', P'_eq⟩ :=
    exists_mem_normalizedFactors_of_dvd hp0 hPirr (Ideal.dvd_iff_le.mpr le)
  rwa [Multiset.count_ne_zero, associated_iff_eq.mp P'_eq]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_zero := ramificationIdx'_ne_zero

中文:
定理 ramificationIdx'_ne_zero
  条件: (hp0 : map f p != ⊥) (hP : P.是素) (le : map f p <= P)
  证明: by
  have hP0 : P != ⊥ := by
    rintro rfl
    exact hp0 (le_bot_iff.mp le)
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0]
  obtain ⟨P', hP', P'_eq⟩ :=
    exists_mem_normalizedFactors_of_dvd hp0 hPirr (Ideal.dvd_iff_le.mpr le)
  rwa [Multiset.count_ne_zero, associated_iff_eq.mp P'_eq]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_zero := ramificationIdx'_ne_zero
-/
theorem ramificationIdx'_ne_zero (hp0 : map f p != ⊥) (hP : P.IsPrime) (le : map f p <= P) :
    ramificationIdx' p P != 0 := by
  have hP0 : P != ⊥ := by
    rintro rfl
    exact hp0 (le_bot_iff.mp le)
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0]
  obtain ⟨P', hP', P'_eq⟩ :=
    exists_mem_normalizedFactors_of_dvd hp0 hPirr (Ideal.dvd_iff_le.mpr le)
  rwa [Multiset.count_ne_zero, associated_iff_eq.mp P'_eq]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_zero := ramificationIdx'_ne_zero

/--
theorem `ramificationIdx'_ne_zero_of_liesOver` / 定理 `ramificationIdx'_ne_zero_of_liesOver`

English:
theorem ramificationIdx'_ne_zero_of_liesOver
  statement: [IsDomain R] [IsTorsionFree R S]
  proof: IsDedekindDomain.ramificationIdx'_ne_zero (map_ne_bot_of_ne_bot hp) hP
map_le_iff_le_comap.mpr le_of_eq (liesOver_iff _ _).mp hPp

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_zero_of_liesOver :=
  ramificationIdx'_ne_zero_of_liesOver

中文:
定理 ramificationIdx'_ne_zero_of_liesOver
  结论: [是整环 R] [是无挠 R S]
  证明: IsDedekindDomain.ramificationIdx'_ne_zero (map_ne_bot_of_ne_bot hp) hP
map_le_iff_le_comap.mpr le_of_eq (liesOver_iff _ _).mp hPp

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_zero_of_liesOver :=
  ramificationIdx'_ne_zero_of_liesOver
-/
theorem ramificationIdx'_ne_zero_of_liesOver [IsDomain R] [IsTorsionFree R S]
    (P : Ideal S) [hP : P.IsPrime] {p : Ideal R} (hp : p != ⊥) [hPp : P.LiesOver p] :
    ramificationIdx' p P != 0 :=
IsDedekindDomain.ramificationIdx'_ne_zero (map_ne_bot_of_ne_bot hp) hP
map_le_iff_le_comap.mpr le_of_eq (liesOver_iff _ _).mp hPp

@[deprecated (since := "2026-07-01")] alias ramificationIdx_ne_zero_of_liesOver :=
  ramificationIdx'_ne_zero_of_liesOver

set_option backward.isDefEq.respectTransparency.types false in
open IsLocalRing in
/--
lemma `ramificationIdx'_eq_one_iff` / 引理 `ramificationIdx'_eq_one_iff`

English:
lemma ramificationIdx'_eq_one_iff
  proof: by
  refine ⟨?_, ramificationIdx'_eq_one_of_map_localization hpP hp (primeCompl_le_nonZeroDivisors _)⟩
  let Sₚ := Localization.AtPrime P
  rw [← not_ne_iff (b := 1)]; rw [ramificationIdx'_ne_one_iff hpP]; rw [pow_two]
  intro H₁
  obtain ⟨a, ha⟩ : P ∣ p.map (algebraMap R S) := Ideal.dvd_iff_le.mpr hpP
  have ha' : ¬ a <= P := fun h => H₁ (ha.trans_le (Ideal.mul_mono_right h))
  rw [IsScalarTower.algebraMap_eq _ S]; rw [← Ideal.map_map]; rw [ha]; rw [Ideal.map_mul]; rw [Localization.AtPrime.map_eq_maximalIdeal]
  convert! Ideal.mul_top _
  on_goal 2 => infer_instance
  rw [← not_ne_iff]; rw [IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl]
  simpa [primeCompl, Set.disjoint_compl_left_iff_subset]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_one_iff :=
  ramificationIdx'_eq_one_iff

中文:
引理 ramificationIdx'_eq_one_iff
  证明: by
  refine ⟨?_, ramificationIdx'_eq_one_of_map_localization hpP hp (primeCompl_le_nonZeroDivisors _)⟩
  let Sₚ := Localization.AtPrime P
  rw [← not_ne_iff (b := 1)]; rw [ramificationIdx'_ne_one_iff hpP]; rw [pow_two]
  intro H₁
  obtain ⟨a, ha⟩ : P ∣ p.map (algebraMap R S) := Ideal.dvd_iff_le.mpr hpP
  have ha' : ¬ a <= P := fun h => H₁ (ha.trans_le (Ideal.mul_mono_right h))
  rw [IsScalarTower.algebraMap_eq _ S]; rw [← Ideal.map_map]; rw [ha]; rw [Ideal.map_mul]; rw [Localization.AtPrime.map_eq_maximalIdeal]
  convert! Ideal.mul_top _
  on_goal 2 => infer_instance
  rw [← not_ne_iff]; rw [IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl]
  simpa [primeCompl, Set.disjoint_compl_left_iff_subset]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_one_iff :=
  ramificationIdx'_eq_one_iff
-/
lemma ramificationIdx'_eq_one_iff
    {p : Ideal R} {P : Ideal S} [P.IsPrime]
    (hp : P != ⊥) (hpP : p.map (algebraMap R S) <= P) :
    ramificationIdx' p P = 1 ↔
      p.map (algebraMap R (Localization.AtPrime P)) = maximalIdeal (Localization.AtPrime P) := by
  refine ⟨?_, ramificationIdx'_eq_one_of_map_localization hpP hp (primeCompl_le_nonZeroDivisors _)⟩
  let Sₚ := Localization.AtPrime P
  rw [← not_ne_iff (b := 1)]; rw [ramificationIdx'_ne_one_iff hpP]; rw [pow_two]
  intro H₁
  obtain ⟨a, ha⟩ : P ∣ p.map (algebraMap R S) := Ideal.dvd_iff_le.mpr hpP
  have ha' : ¬ a <= P := fun h => H₁ (ha.trans_le (Ideal.mul_mono_right h))
  rw [IsScalarTower.algebraMap_eq _ S]; rw [← Ideal.map_map]; rw [ha]; rw [Ideal.map_mul]; rw [Localization.AtPrime.map_eq_maximalIdeal]
  convert! Ideal.mul_top _
  on_goal 2 => infer_instance
  rw [← not_ne_iff]; rw [IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl]
  simpa [primeCompl, Set.disjoint_compl_left_iff_subset]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_one_iff :=
  ramificationIdx'_eq_one_iff

/--
theorem `ramificationIdx'_le_ramificationIdx'` / 定理 `ramificationIdx'_le_ramificationIdx'`

English:
theorem ramificationIdx'_le_ramificationIdx'
  statement: [IsDomain R] [IsTorsionFree R S] {S₀ : Type*}
  proof: p.ramificationIdx'_le_ramificationIdx' P Q ((liesOver_iff ..).mp hP)
    ramificationIdx'_ne_zero_of_liesOver _ hp

@[deprecated (since := "2026-07-01")] alias ramificationIdx_le_ramificationIdx :=
  ramificationIdx'_le_ramificationIdx'

中文:
定理 ramificationIdx'_le_ramificationIdx'
  结论: [是整环 R] [是无挠 R S] {S₀ : 类型}
  证明: p.ramificationIdx'_le_ramificationIdx' P Q ((liesOver_iff ..).mp hP)
    ramificationIdx'_ne_zero_of_liesOver _ hp

@[deprecated (since := "2026-07-01")] alias ramificationIdx_le_ramificationIdx :=
  ramificationIdx'_le_ramificationIdx'
-/
theorem ramificationIdx'_le_ramificationIdx' [IsDomain R] [IsTorsionFree R S] {S₀ : Type*}
    [CommRing S₀] [Algebra R S₀] [Algebra S₀ S] [IsScalarTower R S₀ S] (p : Ideal R)
    (P : Ideal S₀) (Q : Ideal S) [Q.LiesOver p] [hP : P.LiesOver p] [Q.IsPrime] (hp : p != ⊥) :
    Ideal.ramificationIdx' P Q <= Ideal.ramificationIdx' p Q :=
p.ramificationIdx'_le_ramificationIdx' P Q ((liesOver_iff ..).mp hP)
    ramificationIdx'_ne_zero_of_liesOver _ hp

@[deprecated (since := "2026-07-01")] alias ramificationIdx_le_ramificationIdx :=
  ramificationIdx'_le_ramificationIdx'

/--
theorem `emultiplicity_map_eq_zero_of_ne` / 定理 `emultiplicity_map_eq_zero_of_ne`

English:
theorem emultiplicity_map_eq_zero_of_ne
  statement: [IsDedekindDomain R] {v : Ideal R}
  proof: by
  refine emultiplicity_eq_zero.2 fun h => hvp.symm ?_
  rw [Ideal.dvd_iff_le]; rw [Ideal.map_le_iff_le_comap]; rw [← under_def]; rw [← Ideal.over_def w v] at h
  exact ((isPrime_of_prime hp).isMaximal hp.ne_zero).eq_of_le (isPrime_of_prime hv.prime).ne_top h

中文:
定理 emultiplicity_map_eq_zero_of_ne
  结论: [是Dedekind整环 R] {v : 理想 R}
  证明: by
  refine emultiplicity_eq_zero.2 fun h => hvp.symm ?_
  rw [Ideal.dvd_iff_le]; rw [Ideal.map_le_iff_le_comap]; rw [← under_def]; rw [← Ideal.over_def w v] at h
  exact ((isPrime_of_prime hp).isMaximal hp.ne_zero).eq_of_le (isPrime_of_prime hv.prime).ne_top h

Depends on / 依赖: Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, Ideal.over_def, dvd_iff_le, emultiplicity_eq_zero, eq_of_le, hp.ne_zero, hv.prime, hvp.symm, isMaximal, isPrime_of_prime, map_le_iff_le_comap, ne_top, ne_zero, over_def, under_def
-/
theorem emultiplicity_map_eq_zero_of_ne [IsDedekindDomain R] {v : Ideal R}
    {w : Ideal S} {p : Ideal R} (hv : Irreducible v) (hp : Prime p) (hvp : v != p) [w.LiesOver v] :
    emultiplicity w (p.map (algebraMap R S)) = 0 := by
  refine emultiplicity_eq_zero.2 fun h => hvp.symm ?_
  rw [Ideal.dvd_iff_le]; rw [Ideal.map_le_iff_le_comap]; rw [← under_def]; rw [← Ideal.over_def w v] at h
  exact ((isPrime_of_prime hp).isMaximal hp.ne_zero).eq_of_le (isPrime_of_prime hv.prime).ne_top h

/--
theorem `emultiplicity_map_eq_ramificationIdx'_mul_of_prime` / 定理 `emultiplicity_map_eq_ramificationIdx'_mul_of_prime`

English:
theorem emultiplicity_map_eq_ramificationIdx'_mul_of_prime
  statement: [IsDedekindDomain R]
  proof: by
  have hp_bot : p.map (algebraMap R S) != ⊥ := map_ne_bot_of_ne_bot hp.ne_zero
  by_cases hvp : v = p
  · simp [hvp, (FiniteMultiplicity.of_prime_left hp hp.ne_zero).emultiplicity_self,
      ramificationIdx'_eq_normalizedFactors_count hp_bot (isPrime_of_prime hw.prime) hw_bot,
      emultiplicity_eq_count_normalizedFactors hw hp_bot]
  · rw [emultiplicity_eq_zero_of_irreducible_ne hv hp.irreducible hvp, mul_zero,
      emultiplicity_map_eq_zero_of_ne hv hp hvp]

中文:
定理 emultiplicity_map_eq_ramificationIdx'_mul_of_prime
  结论: [是Dedekind整环 R]
  证明: by
  have hp_bot : p.map (algebraMap R S) != ⊥ := map_ne_bot_of_ne_bot hp.ne_zero
  by_cases hvp : v = p
  · simp [hvp, (FiniteMultiplicity.of_prime_left hp hp.ne_zero).emultiplicity_self,
      ramificationIdx'_eq_normalizedFactors_count hp_bot (isPrime_of_prime hw.prime) hw_bot,
      emultiplicity_eq_count_normalizedFactors hw hp_bot]
  · rw [emultiplicity_eq_zero_of_irreducible_ne hv hp.irreducible hvp, mul_zero,
      emultiplicity_map_eq_zero_of_ne hv hp hvp]
-/
private theorem emultiplicity_map_eq_ramificationIdx'_mul_of_prime [IsDedekindDomain R]
    [FaithfulSMul R S] {v : Ideal R} {w : Ideal S} {p : Ideal R}
    (hv : Irreducible v) (hp : Prime p) (hw : Irreducible w) (hw_bot : w != ⊥)
    [w.LiesOver v] : emultiplicity w (p.map (algebraMap R S)) =
      v.ramificationIdx' w * emultiplicity v p := by
  have hp_bot : p.map (algebraMap R S) != ⊥ := map_ne_bot_of_ne_bot hp.ne_zero
  by_cases hvp : v = p
  · simp [hvp, (FiniteMultiplicity.of_prime_left hp hp.ne_zero).emultiplicity_self,
      ramificationIdx'_eq_normalizedFactors_count hp_bot (isPrime_of_prime hw.prime) hw_bot,
      emultiplicity_eq_count_normalizedFactors hw hp_bot]
  · rw [emultiplicity_eq_zero_of_irreducible_ne hv hp.irreducible hvp, mul_zero,
      emultiplicity_map_eq_zero_of_ne hv hp hvp]

/--
theorem `emultiplicity_map_eq_ramificationIdx'_mul` / 定理 `emultiplicity_map_eq_ramificationIdx'_mul`

English:
theorem emultiplicity_map_eq_ramificationIdx'_mul
  statement: [IsDedekindDomain R]
  proof: by
  induction I using induction_on_prime with
  | h₁ => aesop
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp_rw [Ideal.map_top, emultiplicity_eq_count_normalizedFactors hw top_ne_bot,
      emultiplicity_eq_count_normalizedFactors hv h, ← Ideal.one_eq_top, normalizedFactors_one]
    simp
  | h₃ I p hI hp IH =>
    rw [Ideal.map_mul]; rw [emultiplicity_mul hw.prime]; rw [emultiplicity_mul hv.prime]; rw [IH hI]; rw [mul_add]; rw [emultiplicity_map_eq_ramificationIdx'_mul_of_prime hv hp hw hw_bot]

@[deprecated (since := "2026-07-01")] alias emultiplicity_map_eq_ramificationIdx_mul :=
  emultiplicity_map_eq_ramificationIdx'_mul

中文:
定理 emultiplicity_map_eq_ramificationIdx'_mul
  结论: [是Dedekind整环 R]
  证明: by
  induction I using induction_on_prime with
  | h₁ => aesop
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp_rw [Ideal.map_top, emultiplicity_eq_count_normalizedFactors hw top_ne_bot,
      emultiplicity_eq_count_normalizedFactors hv h, ← Ideal.one_eq_top, normalizedFactors_one]
    simp
  | h₃ I p hI hp IH =>
    rw [Ideal.map_mul]; rw [emultiplicity_mul hw.prime]; rw [emultiplicity_mul hv.prime]; rw [IH hI]; rw [mul_add]; rw [emultiplicity_map_eq_ramificationIdx'_mul_of_prime hv hp hw hw_bot]

@[deprecated (since := "2026-07-01")] alias emultiplicity_map_eq_ramificationIdx_mul :=
  emultiplicity_map_eq_ramificationIdx'_mul

Depends on / 依赖: Ideal.map_mul, Ideal.map_top, Ideal.one_eq_top, _mul_of_prime, emultiplicity_eq_count_normalizedFactors, emultiplicity_map_eq_ramificationIdx, emultiplicity_mul, hv.prime, hw.prime, hw_bot, induction_on_prime, map_mul, map_top, mul_add, normalizedFactors_one, one_eq_top, simp_rw, top_ne_bot
-/
theorem emultiplicity_map_eq_ramificationIdx'_mul [IsDedekindDomain R]
    [FaithfulSMul R S] {v : Ideal R} {w : Ideal S} {I : Ideal R} (h : I != ⊥)
    (hv : Irreducible v) (hw : Irreducible w) (hw_bot : w != ⊥) [w.LiesOver v] :
    emultiplicity w (I.map (algebraMap R S)) =
      v.ramificationIdx' w * emultiplicity v I := by
  induction I using induction_on_prime with
  | h₁ => aesop
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp_rw [Ideal.map_top, emultiplicity_eq_count_normalizedFactors hw top_ne_bot,
      emultiplicity_eq_count_normalizedFactors hv h, ← Ideal.one_eq_top, normalizedFactors_one]
    simp
  | h₃ I p hI hp IH =>
    rw [Ideal.map_mul]; rw [emultiplicity_mul hw.prime]; rw [emultiplicity_mul hv.prime]; rw [IH hI]; rw [mul_add]; rw [emultiplicity_map_eq_ramificationIdx'_mul_of_prime hv hp hw hw_bot]

@[deprecated (since := "2026-07-01")] alias emultiplicity_map_eq_ramificationIdx_mul :=
  emultiplicity_map_eq_ramificationIdx'_mul

end IsDedekindDomain

end DecEq

section tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/--
theorem `ramificationIdx'_algebra_tower` / 定理 `ramificationIdx'_algebra_tower`

English:
theorem ramificationIdx'_algebra_tower
  statement: [IsDedekindDomain S] [IsDedekindDomain T]
  proof: by
  have hf0 : map (algebraMap R S) p != ⊥ := by
    rw [IsScalarTower.algebraMap_eq R S T]; rw [← map_map] at hfg
    exact ne_bot_of_map_ne_bot hfg
  have hp0 : P != ⊥ := ne_bot_of_map_ne_bot hg0
  have hq0 : Q != ⊥ := ne_bot_of_le_ne_bot hg0 hg
  let : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp0 hpm
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hf0 hpm hp0]; rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hg0 hqm hq0]; rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hfg hqm hq0]; rw [IsScalarTower.algebraMap_eq R S T]; rw [← map_map]
  rcases eq_prime_pow_mul_coprime hf0 P with ⟨I, hcp, heq⟩
  have hcp : ⊤ = map (algebraMap S T) P ⊔ map (algebraMap S T) I := by rw [← map_sup, hcp, map_top]
  have hntq : ¬ ⊤ <= Q := fun ht => IsPrime.ne_top hqm (Iff.mpr (eq_top_iff_one Q) (ht trivial))
  nth_rw 1 [heq, Ideal.map_mul, Ideal.map_pow, normalizedFactors_mul (pow_ne_zero _ hg0) <| by
    by_contra h
    simp only [h, Submodule.zero_eq_bot, bot_le, sup_of_le_left] at hcp
    exact hntq (hcp.trans_le hg), Multiset.count_add, normalizedFactors_pow, Multiset.count_nsmul]
exact add_eq_left.mpr Decidable.byContradiction fun h => hntq hcp.trans_le
sup_le hg le_of_dvd dvd_of_mem_normalizedFactors Multiset.count_ne_zero.mp h

@[deprecated (since := "2026-07-01")] alias ramificationIdx_algebra_tower :=
  ramificationIdx'_algebra_tower

中文:
定理 ramificationIdx'_algebra_tower
  结论: [是Dedekind整环 S] [是Dedekind整环 T]
  证明: by
  have hf0 : map (algebraMap R S) p != ⊥ := by
    rw [IsScalarTower.algebraMap_eq R S T]; rw [← map_map] at hfg
    exact ne_bot_of_map_ne_bot hfg
  have hp0 : P != ⊥ := ne_bot_of_map_ne_bot hg0
  have hq0 : Q != ⊥ := ne_bot_of_le_ne_bot hg0 hg
  let : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp0 hpm
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hf0 hpm hp0]; rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hg0 hqm hq0]; rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hfg hqm hq0]; rw [IsScalarTower.algebraMap_eq R S T]; rw [← map_map]
  rcases eq_prime_pow_mul_coprime hf0 P with ⟨I, hcp, heq⟩
  have hcp : ⊤ = map (algebraMap S T) P ⊔ map (algebraMap S T) I := by rw [← map_sup, hcp, map_top]
  have hntq : ¬ ⊤ <= Q := fun ht => IsPrime.ne_top hqm (Iff.mpr (eq_top_iff_one Q) (ht trivial))
  nth_rw 1 [heq, Ideal.map_mul, Ideal.map_pow, normalizedFactors_mul (pow_ne_zero _ hg0) <| by
    by_contra h
    simp only [h, Submodule.zero_eq_bot, bot_le, sup_of_le_left] at hcp
    exact hntq (hcp.trans_le hg), Multiset.count_add, normalizedFactors_pow, Multiset.count_nsmul]
exact add_eq_left.mpr Decidable.byContradiction fun h => hntq hcp.trans_le
sup_le hg le_of_dvd dvd_of_mem_normalizedFactors Multiset.count_ne_zero.mp h

@[deprecated (since := "2026-07-01")] alias ramificationIdx_algebra_tower :=
  ramificationIdx'_algebra_tower
-/
theorem ramificationIdx'_algebra_tower [IsDedekindDomain S] [IsDedekindDomain T]
    {p : Ideal R} {P : Ideal S} {Q : Ideal T} [hpm : P.IsPrime] [hqm : Q.IsPrime]
    (hg0 : map (algebraMap S T) P != ⊥)
    (hfg : map (algebraMap R T) p != ⊥) (hg : map (algebraMap S T) P <= Q) :
    ramificationIdx' p Q =
    ramificationIdx' p P * ramificationIdx' P Q := by
  have hf0 : map (algebraMap R S) p != ⊥ := by
    rw [IsScalarTower.algebraMap_eq R S T]; rw [← map_map] at hfg
    exact ne_bot_of_map_ne_bot hfg
  have hp0 : P != ⊥ := ne_bot_of_map_ne_bot hg0
  have hq0 : Q != ⊥ := ne_bot_of_le_ne_bot hg0 hg
  let : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp0 hpm
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hf0 hpm hp0]; rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hg0 hqm hq0]; rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hfg hqm hq0]; rw [IsScalarTower.algebraMap_eq R S T]; rw [← map_map]
  rcases eq_prime_pow_mul_coprime hf0 P with ⟨I, hcp, heq⟩
  have hcp : ⊤ = map (algebraMap S T) P ⊔ map (algebraMap S T) I := by rw [← map_sup, hcp, map_top]
  have hntq : ¬ ⊤ <= Q := fun ht => IsPrime.ne_top hqm (Iff.mpr (eq_top_iff_one Q) (ht trivial))
  nth_rw 1 [heq, Ideal.map_mul, Ideal.map_pow, normalizedFactors_mul (pow_ne_zero _ hg0) <| by
    by_contra h
    simp only [h, Submodule.zero_eq_bot, bot_le, sup_of_le_left] at hcp
    exact hntq (hcp.trans_le hg), Multiset.count_add, normalizedFactors_pow, Multiset.count_nsmul]
exact add_eq_left.mpr Decidable.byContradiction fun h => hntq hcp.trans_le
sup_le hg le_of_dvd dvd_of_mem_normalizedFactors Multiset.count_ne_zero.mp h

@[deprecated (since := "2026-07-01")] alias ramificationIdx_algebra_tower :=
  ramificationIdx'_algebra_tower

/--
theorem `ramificationIdx'_algebra_tower'` / 定理 `ramificationIdx'_algebra_tower'`

English:
theorem ramificationIdx'_algebra_tower'
  statement: [IsDedekindDomain S] [IsDedekindDomain T] [IsDomain R]
  proof: by
  obtain rfl | hp := eq_or_ne p ⊥
  · simp
  have : P.IsPrime := isPrime_of_liesOver Q P
  have : Module.IsTorsionFree R T := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    rwa [algebra_compatible_smul S, smul_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff] at h
  have hP : P != ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  exact ramificationIdx'_algebra_tower (map_ne_bot_of_ne_bot hP) (map_ne_bot_of_ne_bot hp)
 map_le_iff_le_comap.mpr le_of_eq over_def Q P

@[deprecated (since := "2026-07-01")] alias ramificationIdx_algebra_tower' :=
  ramificationIdx'_algebra_tower'

中文:
定理 ramificationIdx'_algebra_tower'
  结论: [是Dedekind整环 S] [是Dedekind整环 T] [是整环 R]
  证明: by
  obtain rfl | hp := eq_or_ne p ⊥
  · simp
  have : P.IsPrime := isPrime_of_liesOver Q P
  have : Module.IsTorsionFree R T := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    rwa [algebra_compatible_smul S, smul_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff] at h
  have hP : P != ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  exact ramificationIdx'_algebra_tower (map_ne_bot_of_ne_bot hP) (map_ne_bot_of_ne_bot hp)
 map_le_iff_le_comap.mpr le_of_eq over_def Q P

@[deprecated (since := "2026-07-01")] alias ramificationIdx_algebra_tower' :=
  ramificationIdx'_algebra_tower'
-/
theorem ramificationIdx'_algebra_tower' [IsDedekindDomain S] [IsDedekindDomain T] [IsDomain R]
    [Module.IsTorsionFree R S] [Module.IsTorsionFree S T] (p : Ideal R) (P : Ideal S) (Q : Ideal T)
    [Q.IsPrime] [Q.LiesOver P] [P.LiesOver p] :
    ramificationIdx' p Q =
      ramificationIdx' p P * ramificationIdx' P Q := by
  obtain rfl | hp := eq_or_ne p ⊥
  · simp
  have : P.IsPrime := isPrime_of_liesOver Q P
  have : Module.IsTorsionFree R T := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    rwa [algebra_compatible_smul S, smul_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff] at h
  have hP : P != ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  exact ramificationIdx'_algebra_tower (map_ne_bot_of_ne_bot hP) (map_ne_bot_of_ne_bot hp)
 map_le_iff_le_comap.mpr le_of_eq over_def Q P

@[deprecated (since := "2026-07-01")] alias ramificationIdx_algebra_tower' :=
  ramificationIdx'_algebra_tower'

end tower

end Ideal
