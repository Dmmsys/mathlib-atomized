/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Data.Multiset.Fold

/-!
# Multisets form an ordered monoid

This file contains the ordered monoid instance on multisets, and lemmas related to it.

See note [foundational algebra order theory].
-/

@[expose] public section

open List Nat

variable {α β : Type*}

namespace Multiset


/--
Instance `instAddLeftMono` / 实例 `instAddLeftMono`

English:
instance instAddLeftMono
  signature: : AddLeftMono (Multiset α) where elim _s _t _u
  body: Multiset.add_le_add_left

中文:
实例 instAddLeftMono
  签名: : AddLeftMono (Multiset α) where elim _s _t _u
  定义体: Multiset.add_le_add_left

Depends on / 依赖: Multiset, Multiset.add_le_add_left, add_le_add_left
-/
instance instAddLeftMono : AddLeftMono (Multiset α) where elim _s _t _u := Multiset.add_le_add_left

/--
Instance `instAddLeftReflectLE` / 实例 `instAddLeftReflectLE`

English:
instance instAddLeftReflectLE
  signature: : AddLeftReflectLE (Multiset α) where
  body: Multiset.le_of_add_le_add_left

中文:
实例 instAddLeftReflectLE
  签名: : AddLeftReflectLE (Multiset α) where
  定义体: Multiset.le_of_add_le_add_left

Depends on / 依赖: Multiset, Multiset.le_of_add_le_add_left, le_of_add_le_add_left
-/
instance instAddLeftReflectLE : AddLeftReflectLE (Multiset α) where
  le_of_add_le_add_left := Multiset.le_of_add_le_add_left

/--
Instance `instAddCancelCommMonoid` / 实例 `instAddCancelCommMonoid`

English:
instance instAddCancelCommMonoid
  signature: : AddCancelCommMonoid (Multiset α) where
  body: Multiset.add_comm
  add_assoc := Multiset.add_assoc
  zero_add := Multiset.zero_add
  add_zero := Multiset.add_zero
  add_left_cancel _ _ _ := Multiset.add_right_inj.1
  nsmul := nsmulRec

中文:
实例 instAddCancelCommMonoid
  签名: : AddCancelCommMonoid (Multiset α) where
  定义体: Multiset.add_comm
  add_assoc := Multiset.add_assoc
  zero_add := Multiset.zero_add
  add_zero := Multiset.add_zero
  add_left_cancel _ _ _ := Multiset.add_right_inj.1
  nsmul := nsmulRec

Depends on / 依赖: Multiset, Multiset.add_comm, add_comm
-/
instance instAddCancelCommMonoid : AddCancelCommMonoid (Multiset α) where
  add_comm := Multiset.add_comm
  add_assoc := Multiset.add_assoc
  zero_add := Multiset.zero_add
  add_zero := Multiset.add_zero
  add_left_cancel _ _ _ := Multiset.add_right_inj.1
  nsmul := nsmulRec

/--
lemma `mem_of_mem_nsmul` / 引理 `mem_of_mem_nsmul`

English:
lemma mem_of_mem_nsmul
  given: {a : α} {s : Multiset α} {n : Nat} (h : a in n • s)
  statement: a in s
  proof: by
  induction n with
  | zero =>
    rw [zero_nsmul] at h
    exact absurd h (notMem_zero _)
  | succ n ih =>
    rw [succ_nsmul]; rw [mem_add] at h
    exact h.elim ih id

@[simp]

中文:
引理 mem_of_mem_nsmul
  条件: {a : α} {s : Multiset α} {n : 自然数} (h : a in n • s)
  结论: a in s
  证明: by
  induction n with
  | zero =>
    rw [zero_nsmul] at h
    exact absurd h (notMem_zero _)
  | succ n ih =>
    rw [succ_nsmul]; rw [mem_add] at h
    exact h.elim ih id

@[simp]

Depends on / 依赖: absurd, h.elim, mem_add, notMem_zero, succ_nsmul, zero_nsmul
-/
lemma mem_of_mem_nsmul {a : α} {s : Multiset α} {n : Nat} (h : a in n • s) : a in s := by
  induction n with
  | zero =>
    rw [zero_nsmul] at h
    exact absurd h (notMem_zero _)
  | succ n ih =>
    rw [succ_nsmul]; rw [mem_add] at h
    exact h.elim ih id

@[simp]
/--
lemma `mem_nsmul` / 引理 `mem_nsmul`

English:
lemma mem_nsmul
  given: {a : α} {s : Multiset α} {n : Nat}
  statement: a in n • s ↔ n != 0 ∧ a in s
  proof: by
  refine ⟨fun ha => ⟨?_, mem_of_mem_nsmul ha⟩, fun h => ?_⟩
  · rintro rfl
    simp [zero_nsmul] at ha
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero h.1
  rw [succ_nsmul]; rw [mem_add]
  exact Or.inr h.2

中文:
引理 mem_nsmul
  条件: {a : α} {s : Multiset α} {n : 自然数}
  结论: a in n • s ↔ n != 0 ∧ a in s
  证明: by
  refine ⟨fun ha => ⟨?_, mem_of_mem_nsmul ha⟩, fun h => ?_⟩
  · rintro rfl
    simp [zero_nsmul] at ha
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero h.1
  rw [succ_nsmul]; rw [mem_add]
  exact Or.inr h.2

Depends on / 依赖: Or.inr, exists_eq_succ_of_ne_zero, mem_add, mem_of_mem_nsmul, succ_nsmul, zero_nsmul
-/
lemma mem_nsmul {a : α} {s : Multiset α} {n : Nat} : a in n • s ↔ n != 0 ∧ a in s := by
  refine ⟨fun ha => ⟨?_, mem_of_mem_nsmul ha⟩, fun h => ?_⟩
  · rintro rfl
    simp [zero_nsmul] at ha
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero h.1
  rw [succ_nsmul]; rw [mem_add]
  exact Or.inr h.2

/--
lemma `mem_nsmul_of_ne_zero` / 引理 `mem_nsmul_of_ne_zero`

English:
lemma mem_nsmul_of_ne_zero
  given: {a : α} {s : Multiset α} {n : Nat} (h0 : n != 0)
  statement: a in n • s ↔ a in s
  proof: by
  simp [*]

中文:
引理 mem_nsmul_of_ne_zero
  条件: {a : α} {s : Multiset α} {n : 自然数} (h0 : n != 0)
  结论: a in n • s ↔ a in s
  证明: by
  simp [*]
-/
lemma mem_nsmul_of_ne_zero {a : α} {s : Multiset α} {n : Nat} (h0 : n != 0) : a in n • s ↔ a in s := by
  simp [*]

/--
theorem `smul_subset_self` / 定理 `smul_subset_self`

English:
theorem smul_subset_self
  given: (s : Multiset α) (n : Nat)
  statement: n • s subseteq s
  proof: subset_iff.mpr fun _ => mem_of_mem_nsmul

中文:
定理 smul_subset_self
  条件: (s : Multiset α) (n : 自然数)
  结论: n • s subseteq s
  证明: subset_iff.mpr fun _ => mem_of_mem_nsmul

Depends on / 依赖: mem_of_mem_nsmul, subset_iff, subset_iff.mpr
-/
theorem smul_subset_self (s : Multiset α) (n : Nat) : n • s subseteq s :=
  subset_iff.mpr fun _ => mem_of_mem_nsmul

/--
theorem `subset_smul_self_of_ne_zero` / 定理 `subset_smul_self_of_ne_zero`

English:
theorem subset_smul_self_of_ne_zero
  given: (s : Multiset α) {n : Nat} (hn : n != 0)
  statement: s subseteq n • s
  proof: .mpr subset_iff.mpr fun _ => mem_nsmul_of_ne_zero hn

中文:
定理 subset_smul_self_of_ne_zero
  条件: (s : Multiset α) {n : 自然数} (hn : n != 0)
  结论: s subseteq n • s
  证明: .mpr subset_iff.mpr fun _ => mem_nsmul_of_ne_zero hn

Depends on / 依赖: mem_nsmul_of_ne_zero, subset_iff, subset_iff.mpr
-/
theorem subset_smul_self_of_ne_zero (s : Multiset α) {n : Nat} (hn : n != 0) : s subseteq n • s :=
.mpr subset_iff.mpr fun _ => mem_nsmul_of_ne_zero hn

/--
lemma `nsmul_cons` / 引理 `nsmul_cons`

English:
lemma nsmul_cons
  given: {s : Multiset α} (n : Nat) (a : α)
  proof: by
  rw [← singleton_add]; rw [nsmul_add]

中文:
引理 nsmul_cons
  条件: {s : Multiset α} (n : 自然数) (a : α)
  证明: by
  rw [← singleton_add]; rw [nsmul_add]

Depends on / 依赖: nsmul_add, singleton_add
-/
lemma nsmul_cons {s : Multiset α} (n : Nat) (a : α) :
    n • (a ::ₘ s) = n • ({a} : Multiset α) + n • s := by
  rw [← singleton_add]; rw [nsmul_add]

/-! ### Cardinality -/

/-- `Multiset.card` bundled as a group hom. -/
@[simps]
/--
Definition of `cardHom` / `cardHom` 的定义

English:
definition cardHom
  signature: : Multiset α ->+ Nat where
  body: card
  map_zero' := card_zero
  map_add' := card_add

@[simp]

中文:
定义 cardHom
  签名: : Multiset α ->+ 自然数 where
  定义体: card
  map_zero' := card_zero
  map_add' := card_add

@[simp]
-/
def cardHom : Multiset α ->+ Nat where
  toFun := card
  map_zero' := card_zero
  map_add' := card_add

@[simp]
/--
lemma `card_nsmul` / 引理 `card_nsmul`

English:
lemma card_nsmul
  given: (s : Multiset α) (n : Nat)
  statement: card (n • s) = n * card s
  proof: cardHom.map_nsmul ..

中文:
引理 card_nsmul
  条件: (s : Multiset α) (n : 自然数)
  结论: card (n • s) = n * card s
  证明: cardHom.map_nsmul ..

Depends on / 依赖: cardHom, cardHom.map_nsmul, map_nsmul
-/
lemma card_nsmul (s : Multiset α) (n : Nat) : card (n • s) = n * card s := cardHom.map_nsmul ..

/-! ### `Multiset.replicate` -/

/-- `Multiset.replicate` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `replicateAddMonoidHom` / `replicateAddMonoidHom` 的定义

English:
definition replicateAddMonoidHom
  signature: (a : α)
  body: replicate n a
  map_zero' := replicate_zero a
  map_add' _ _ := replicate_add _ _ a

中文:
定义 replicateAddMonoidHom
  签名: (a : α)
  定义体: replicate n a
  map_zero' := replicate_zero a
  map_add' _ _ := replicate_add _ _ a

Depends on / 依赖: replicate
-/
def replicateAddMonoidHom (a : α) : Nat ->+ Multiset α where
  toFun n := replicate n a
  map_zero' := replicate_zero a
  map_add' _ _ := replicate_add _ _ a

/--
lemma `nsmul_replicate` / 引理 `nsmul_replicate`

English:
lemma nsmul_replicate
  given: {a : α} (n m : Nat)
  statement: n • replicate m a = replicate (n * m) a
  proof: ((replicateAddMonoidHom a).map_nsmul _ _).symm

中文:
引理 nsmul_replicate
  条件: {a : α} (n m : 自然数)
  结论: n • replicate m a = replicate (n * m) a
  证明: ((replicateAddMonoidHom a).map_nsmul _ _).symm

Depends on / 依赖: map_nsmul, replicateAddMonoidHom
-/
lemma nsmul_replicate {a : α} (n m : Nat) : n • replicate m a = replicate (n * m) a :=
  ((replicateAddMonoidHom a).map_nsmul _ _).symm

/--
lemma `nsmul_singleton` / 引理 `nsmul_singleton`

English:
lemma nsmul_singleton
  given: (a : α) (n)
  statement: n • ({a} : Multiset α) = replicate n a
  proof: by
  rw [← replicate_one]; rw [nsmul_replicate]; rw [mul_one]

中文:
引理 nsmul_singleton
  条件: (a : α) (n)
  结论: n • ({a} : Multiset α) = replicate n a
  证明: by
  rw [← replicate_one]; rw [nsmul_replicate]; rw [mul_one]

Depends on / 依赖: mul_one, nsmul_replicate, replicate_one
-/
lemma nsmul_singleton (a : α) (n) : n • ({a} : Multiset α) = replicate n a := by
  rw [← replicate_one]; rw [nsmul_replicate]; rw [mul_one]

/-! ### `Multiset.map` -/

/-- `Multiset.map` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `mapAddMonoidHom` / `mapAddMonoidHom` 的定义

English:
definition mapAddMonoidHom
  signature: (f : α -> β)
  body: map f
  map_zero' := map_zero _
  map_add' := map_add _

@[simp]

中文:
定义 mapAddMonoidHom
  签名: (f : α -> β)
  定义体: map f
  map_zero' := map_zero _
  map_add' := map_add _

@[simp]
-/
def mapAddMonoidHom (f : α -> β) : Multiset α ->+ Multiset β where
  toFun := map f
  map_zero' := map_zero _
  map_add' := map_add _

@[simp]
/--
lemma `coe_mapAddMonoidHom` / 引理 `coe_mapAddMonoidHom`

English:
lemma coe_mapAddMonoidHom
  given: (f : α -> β)
  statement: (mapAddMonoidHom f : Multiset α -> Multiset β) = map f
  proof: rfl

中文:
引理 coe_mapAddMonoidHom
  条件: (f : α -> β)
  结论: (mapAddMonoidHom f : Multiset α -> Multiset β) = map f
  证明: rfl
-/
lemma coe_mapAddMonoidHom (f : α -> β) : (mapAddMonoidHom f : Multiset α -> Multiset β) = map f := rfl

/--
lemma `map_nsmul` / 引理 `map_nsmul`

English:
lemma map_nsmul
  given: (f : α -> β) (n : Nat) (s)
  statement: map f (n • s) = n • map f s
  proof: (mapAddMonoidHom f).map_nsmul _ _

中文:
引理 map_nsmul
  条件: (f : α -> β) (n : 自然数) (s)
  结论: map f (n • s) = n • map f s
  证明: (mapAddMonoidHom f).map_nsmul _ _

Depends on / 依赖: mapAddMonoidHom, map_nsmul
-/
lemma map_nsmul (f : α -> β) (n : Nat) (s) : map f (n • s) = n • map f s :=
  (mapAddMonoidHom f).map_nsmul _ _

/-! ### Subtraction -/

section
variable [DecidableEq α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderedSub (Multiset α)
  body: Multiset.sub_le_iff_le_add

中文:
实例 :
  签名: OrderedSub (Multiset α)
  定义体: Multiset.sub_le_iff_le_add

Depends on / 依赖: Multiset, Multiset.sub_le_iff_le_add, sub_le_iff_le_add
-/
instance : OrderedSub (Multiset α) where tsub_le_iff_right _n _m _k := Multiset.sub_le_iff_le_add

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ExistsAddOfLE (Multiset α)
  body: leInductionOn h fun s =>
      let ⟨l, p⟩ := s.exists_perm_append; ⟨l, Quot.sound p⟩

中文:
实例 :
  签名: ExistsAddOfLE (Multiset α)
  定义体: leInductionOn h fun s =>
      let ⟨l, p⟩ := s.exists_perm_append; ⟨l, Quot.sound p⟩

Depends on / 依赖: leInductionOn
-/
instance : ExistsAddOfLE (Multiset α) where
  exists_add_of_le h := leInductionOn h fun s =>
      let ⟨l, p⟩ := s.exists_perm_append; ⟨l, Quot.sound p⟩

end

/-! ### `Multiset.filter` -/

section
variable (p : α -> Prop) [DecidablePred p]

/--
lemma `filter_nsmul` / 引理 `filter_nsmul`

English:
lemma filter_nsmul
  given: (s : Multiset α) (n : Nat)
  statement: filter p (n • s) = n • filter p s
  proof: by
  refine s.induction_on ?_ ?_
  · simp only [filter_zero, nsmul_zero]
  · intro a ha ih
    rw [nsmul_cons]; rw [filter_add]; rw [ih]; rw [filter_cons]; rw [nsmul_add]
    congr
    split_ifs with hp <;>
      · simp only [filter_eq_self, nsmul_zero, filter_eq_nil]
        intro b hb
        rwa 

中文:
引理 filter_nsmul
  条件: (s : Multiset α) (n : 自然数)
  结论: filter p (n • s) = n • filter p s
  证明: by
  refine s.induction_on ?_ ?_
  · simp only [filter_zero, nsmul_zero]
  · intro a ha ih
    rw [nsmul_cons]; rw [filter_add]; rw [ih]; rw [filter_cons]; rw [nsmul_add]
    congr
    split_ifs with hp <;>
      · simp only [filter_eq_self, nsmul_zero, filter_eq_nil]
        intro b hb
        rwa 

Depends on / 依赖: filter_add, filter_cons, filter_eq_nil, filter_eq_self, filter_zero, induction_on, mem_of_mem_nsmul, mem_singleton, mem_singleton.mp, nsmul_add, nsmul_cons, nsmul_zero, s.induction_on, split_ifs
-/
lemma filter_nsmul (s : Multiset α) (n : Nat) : filter p (n • s) = n • filter p s := by
  refine s.induction_on ?_ ?_
  · simp only [filter_zero, nsmul_zero]
  · intro a ha ih
    rw [nsmul_cons]; rw [filter_add]; rw [ih]; rw [filter_cons]; rw [nsmul_add]
    congr
    split_ifs with hp <;>
      · simp only [filter_eq_self, nsmul_zero, filter_eq_nil]
        intro b hb
        rwa [mem_singleton.mp (mem_of_mem_nsmul hb)]

/-! ### countP -/

@[simp]
/--
lemma `countP_nsmul` / 引理 `countP_nsmul`

English:
lemma countP_nsmul
  given: (s) (n : Nat)
  statement: countP p (n • s) = n * countP p s
  proof: by
  induction n <;> simp [*, succ_nsmul, succ_mul, zero_nsmul]

中文:
引理 countP_nsmul
  条件: (s) (n : 自然数)
  结论: countP p (n • s) = n * countP p s
  证明: by
  induction n <;> simp [*, succ_nsmul, succ_mul, zero_nsmul]

Depends on / 依赖: succ_mul, succ_nsmul, zero_nsmul
-/
lemma countP_nsmul (s) (n : Nat) : countP p (n • s) = n * countP p s := by
  induction n <;> simp [*, succ_nsmul, succ_mul, zero_nsmul]

/--
Definition of `countPAddMonoidHom` / `countPAddMonoidHom` 的定义

English:
definition countPAddMonoidHom
  signature: : Multiset α ->+ Nat where
  body: countP p
  map_zero' := countP_zero _
  map_add' := countP_add _

中文:
定义 countPAddMonoidHom
  签名: : Multiset α ->+ 自然数 where
  定义体: countP p
  map_zero' := countP_zero _
  map_add' := countP_add _

Depends on / 依赖: countP
-/
def countPAddMonoidHom : Multiset α ->+ Nat where
  toFun := countP p
  map_zero' := countP_zero _
  map_add' := countP_add _

/--
lemma `coe_countPAddMonoidHom` / 引理 `coe_countPAddMonoidHom`

English:
lemma coe_countPAddMonoidHom
  statement: (countPAddMonoidHom p : Multiset α -> Nat) = countP p
  proof: rfl

中文:
引理 coe_countPAddMonoidHom
  结论: (countPAddMonoidHom p : Multiset α -> 自然数) = countP p
  证明: rfl

Depends on / 依赖: PosMulMono, PosMulMono.toPosSMulMono, PosSMulMono, toPosSMulMono
-/
@[simp] lemma coe_countPAddMonoidHom : (countPAddMonoidHom p : Multiset α -> Nat) = countP p := rfl

end

/--
lemma `dedup_nsmul` / 引理 `dedup_nsmul`

English:
lemma dedup_nsmul
  given: [DecidableEq α] {s : Multiset α} {n : Nat} (hn : n != 0)
  proof: by ext a; by_cases h : a in s <;> simp [h, hn]

中文:
引理 dedup_nsmul
  条件: [DecidableEq α] {s : Multiset α} {n : 自然数} (hn : n != 0)
  证明: by ext a; by_cases h : a in s <;> simp [h, hn]

Depends on / 依赖: PosMulStrictMono, PosMulStrictMono.toPosSMulStrictMono, toPosSMulStrictMono
-/
@[simp] lemma dedup_nsmul [DecidableEq α] {s : Multiset α} {n : Nat} (hn : n != 0) :
    (n • s).dedup = s.dedup := by ext a; by_cases h : a in s <;> simp [h, hn]

/--
lemma `Nodup.le_nsmul_iff_le` / 引理 `Nodup.le_nsmul_iff_le`

English:
lemma Nodup.le_nsmul_iff_le
  given: {s t : Multiset α} {n : Nat} (h : s.Nodup) (hn : n != 0)
  proof: by
  classical simp [← h.le_dedup_iff_le, hn]

中文:
引理 Nodup.le_nsmul_iff_le
  条件: {s t : Multiset α} {n : 自然数} (h : s.Nodup) (hn : n != 0)
  证明: by
  classical simp [← h.le_dedup_iff_le, hn]

Depends on / 依赖: PosMulReflectLT, PosMulReflectLT.toPosSMulReflectLT, classical, h.le_dedup_iff_le, le_dedup_iff_le, toPosSMulReflectLT
-/
lemma Nodup.le_nsmul_iff_le {s t : Multiset α} {n : Nat} (h : s.Nodup) (hn : n != 0) :
    s <= n • t ↔ s <= t := by
  classical simp [← h.le_dedup_iff_le, hn]

/-! ### Multiplicity of an element -/

section
variable [DecidableEq α] {s : Multiset α}

/--
Definition of `countAddMonoidHom` / `countAddMonoidHom` 的定义

English:
definition countAddMonoidHom
  signature: (a : α)
  body: countPAddMonoidHom (a = ·)

@[simp]

中文:
定义 countAddMonoidHom
  签名: (a : α)
  定义体: countPAddMonoidHom (a = ·)

@[simp]

Depends on / 依赖: PosMulReflectLE, PosMulReflectLE.toPosSMulReflectLE, countPAddMonoidHom, toPosSMulReflectLE
-/
def countAddMonoidHom (a : α) : Multiset α ->+ Nat :=
  countPAddMonoidHom (a = ·)

@[simp]
/--
lemma `coe_countAddMonoidHom` / 引理 `coe_countAddMonoidHom`

English:
lemma coe_countAddMonoidHom
  given: (a : α)
  statement: (countAddMonoidHom a : Multiset α -> Nat) = count a
  proof: rfl

@[simp]

中文:
引理 coe_countAddMonoidHom
  条件: (a : α)
  结论: (countAddMonoidHom a : Multiset α -> 自然数) = count a
  证明: rfl

@[simp]

Depends on / 依赖: MulPosMono, MulPosMono.toSMulPosMono, SMulPosMono, toSMulPosMono
-/
lemma coe_countAddMonoidHom (a : α) : (countAddMonoidHom a : Multiset α -> Nat) = count a := rfl

@[simp]
/--
lemma `count_nsmul` / 引理 `count_nsmul`

English:
lemma count_nsmul
  given: (a : α) (n s)
  statement: count a (n • s) = n * count a s
  proof: by
  induction n <;> simp [*, succ_nsmul, succ_mul, zero_nsmul]

中文:
引理 count_nsmul
  条件: (a : α) (n s)
  结论: count a (n • s) = n * count a s
  证明: by
  induction n <;> simp [*, succ_nsmul, succ_mul, zero_nsmul]

Depends on / 依赖: MulPosStrictMono, MulPosStrictMono.toSMulPosStrictMono, succ_mul, succ_nsmul, toSMulPosStrictMono, zero_nsmul
-/
lemma count_nsmul (a : α) (n s) : count a (n • s) = n * count a s := by
  induction n <;> simp [*, succ_nsmul, succ_mul, zero_nsmul]

end

/--
theorem `le_card_smul_iff_subset` / 定理 `le_card_smul_iff_subset`

English:
theorem le_card_smul_iff_subset
  given: {s t : Multiset α}
  statement: s <= s.card • t ↔ s subseteq t
  proof: by
  classical
  refine ⟨fun hle => Subset.trans (subset_of_le hle) (t.smul_subset_self s.card), ?_⟩
  refine fun hsub => le_iff_count.mpr fun a => ?_
  by_cases! has : a ∉ s
  · simp [count_eq_zero_of_notMem has]
  grw [count_le_card, count_nsmul, ← one_le_count_iff_mem.mpr <| mem_of_subset hsub ha

中文:
定理 le_card_smul_iff_subset
  条件: {s t : Multiset α}
  结论: s <= s.card • t ↔ s subseteq t
  证明: by
  classical
  refine ⟨fun hle => Subset.trans (subset_of_le hle) (t.smul_subset_self s.card), ?_⟩
  refine fun hsub => le_iff_count.mpr fun a => ?_
  by_cases! has : a ∉ s
  · simp [count_eq_zero_of_notMem has]
  grw [count_le_card, count_nsmul, ← one_le_count_iff_mem.mpr <| mem_of_subset hsub ha

Depends on / 依赖: MulPosReflectLT, MulPosReflectLT.toSMulPosReflectLT, Subset, Subset.trans, classical, count_eq_zero_of_notMem, count_le_card, count_nsmul, le_iff_count, le_iff_count.mpr, mem_of_subset, mul_one, one_le_count_iff_mem, one_le_count_iff_mem.mpr, s.card, smul_subset_self, subset_of_le, t.smul_subset_self, toSMulPosReflectLT
-/
theorem le_card_smul_iff_subset {s t : Multiset α} : s <= s.card • t ↔ s subseteq t := by
  classical
  refine ⟨fun hle => Subset.trans (subset_of_le hle) (t.smul_subset_self s.card), ?_⟩
  refine fun hsub => le_iff_count.mpr fun a => ?_
  by_cases! has : a ∉ s
  · simp [count_eq_zero_of_notMem has]
  grw [count_le_card, count_nsmul, ← one_le_count_iff_mem.mpr <| mem_of_subset hsub has, mul_one]

-- TODO: This should be `addMonoidHom_ext`
@[ext]
/--
lemma `addHom_ext` / 引理 `addHom_ext`

English:
lemma addHom_ext
  given: [AddZeroClass β] ⦃f g
  statement: Multiset α ->+ β⦄ (h : forall x, f {x} = g {x}) : f = g
  proof: by
  ext s
  induction s using Multiset.induction_on with
  | empty => simp only [_root_.map_zero]
  | cons a s ih => simp only [← singleton_add, _root_.map_add, ih, h]

中文:
引理 addHom_ext
  条件: [AddZeroClass β] ⦃f g
  结论: Multiset α ->+ β⦄ (h : 对任意 x, f {x} = g {x}) : f = g
  证明: by
  ext s
  induction s using Multiset.induction_on with
  | empty => simp only [_root_.map_zero]
  | cons a s ih => simp only [← singleton_add, _root_.map_add, ih, h]

Depends on / 依赖: MulPosReflectLE, MulPosReflectLE.toSMulPosReflectLE, Multiset, Multiset.induction_on, _root_, _root_.map_add, _root_.map_zero, induction_on, map_add, map_zero, singleton_add, toSMulPosReflectLE
-/
lemma addHom_ext [AddZeroClass β] ⦃f g : Multiset α ->+ β⦄ (h : forall x, f {x} = g {x}) : f = g := by
  ext s
  induction s using Multiset.induction_on with
  | empty => simp only [_root_.map_zero]
  | cons a s ih => simp only [← singleton_add, _root_.map_add, ih, h]

/--
theorem `le_smul_dedup` / 定理 `le_smul_dedup`

English:
theorem le_smul_dedup
  given: [DecidableEq α] (s : Multiset α)
  statement: exists n : Nat, s <= n • dedup s
  proof: ⟨s.card, le_card_smul_iff_subset.mpr s.subset_dedup⟩

中文:
定理 le_smul_dedup
  条件: [DecidableEq α] (s : Multiset α)
  结论: 存在 n : 自然数, s <= n • dedup s
  证明: ⟨s.card, le_card_smul_iff_subset.mpr s.subset_dedup⟩

Depends on / 依赖: le_card_smul_iff_subset, le_card_smul_iff_subset.mpr, nsmul_le_nsmul_right, s.card, s.subset_dedup, subset_dedup
-/
theorem le_smul_dedup [DecidableEq α] (s : Multiset α) : exists n : Nat, s <= n • dedup s :=
  ⟨s.card, le_card_smul_iff_subset.mpr s.subset_dedup⟩

end Multiset
