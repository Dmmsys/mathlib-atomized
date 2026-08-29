/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/
module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Rel
public import Mathlib.Order.OrderIsoNat

/-!
# Series of a relation

If `r` is a relation on `α` then a relation series of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`

-/

@[expose] public section

open scoped SetRel

variable {α : Type*} (r : SetRel α α)
variable {β : Type*} (s : SetRel β β)

/--
Definition of `RelSeries` / `RelSeries` 的定义

English:
structure RelSeries
  parameters: where
  axioms and operations (3):
    - length : Nat
    - toFun : Fin (length + 1) -> α
    - step : forall (i : Fin length), toFun (Fin.castSucc i) ~[r] toFun i.succ

中文:
结构 RelSeries
  参数: where
  公理与运算 (3 个):
    - length : 自然数
    - toFun : 有限集 (length + 1) -> α
    - step : 对任意 (i : 有限集 length), toFun (有限集.castSucc i) ~[r] toFun i.succ
-/
structure RelSeries where
  /-- The number of inequalities in the series -/
  length : Nat
  /-- The underlying function of a relation series -/
  toFun : Fin (length + 1) -> α
  /-- Adjacent elements are related -/
  step : forall (i : Fin length), toFun (Fin.castSucc i) ~[r] toFun i.succ

namespace RelSeries

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (RelSeries r) (fun x => Fin (x.length + 1) -> α)
  body: { coe := RelSeries.toFun }

中文:
实例 :
  签名: CoeFun (RelSeries r) (fun x => 有限集 (x.length + 1) -> α)
  定义体: { coe := RelSeries.toFun }

Depends on / 依赖: RelSeries, RelSeries.toFun
-/
instance : CoeFun (RelSeries r) (fun x => Fin (x.length + 1) -> α) :=
{ coe := RelSeries.toFun }

/--
Definition of `singleton` / `singleton` 的定义

English:
definition singleton
  signature: (a : α)
  body: 0
  toFun _ := a
  step := Fin.elim0

中文:
定义 singleton
  签名: (a : α)
  定义体: 0
  toFun _ := a
  step := Fin.elim0
-/
@[simps!] def singleton (a : α) : RelSeries r where
  length := 0
  toFun _ := a
  step := Fin.elim0

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : IsEmpty (RelSeries r) where
  body: IsEmpty.false (x 0)

中文:
实例 [是空
  签名: α] : 是空 (RelSeries r) where
  定义体: IsEmpty.false (x 0)

Depends on / 依赖: IsEmpty, IsEmpty.false
-/
instance [IsEmpty α] : IsEmpty (RelSeries r) where
  false x := IsEmpty.false (x 0)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (RelSeries r) where
  body: singleton r default

中文:
实例 [可居
  签名: α] : 可居 (RelSeries r) where
  定义体: singleton r default

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_reduced_fraction, singleton
-/
instance [Inhabited α] : Inhabited (RelSeries r) where
  default := singleton r default

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nonempty (RelSeries r)
  body: Nonempty.map (singleton r) inferInstance

中文:
实例 [非空
  签名: α] : 非空 (RelSeries r)
  定义体: Nonempty.map (singleton r) inferInstance

Depends on / 依赖: Nonempty, Nonempty.map, _eq_div, _num_den, singleton
-/
instance [Nonempty α] : Nonempty (RelSeries r) :=
  Nonempty.map (singleton r) inferInstance

variable {r}

@[ext (iff := false)]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {x y : RelSeries r} (length_eq : x.length = y.length)
  proof: by
  rcases x with ⟨nx, fx⟩
  dsimp only at length_eq
  subst length_eq
  simp_all

中文:
引理 ext
  结论: {x y : RelSeries r} (length_eq : x.length = y.length)
  证明: by
  rcases x with ⟨nx, fx⟩
  dsimp only at length_eq
  subst length_eq
  simp_all

Depends on / 依赖: length_eq
-/
lemma ext {x y : RelSeries r} (length_eq : x.length = y.length)
    (toFun_eq : x.toFun = y.toFun ∘ Fin.cast (by rw [length_eq])) : x = y := by
  rcases x with ⟨nx, fx⟩
  dsimp only at length_eq
  subst length_eq
  simp_all

/--
lemma `rel_of_lt` / 引理 `rel_of_lt`

English:
lemma rel_of_lt
  given: [r.IsTrans] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i < j)
  proof: (Fin.liftFun_iff_succ (· ~[r] ·)).mpr x.step h

中文:
引理 rel_of_lt
  条件: [r.是Trans] (x : RelSeries r) {i j : 有限集 (x.length + 1)} (h : i < j)
  证明: (Fin.liftFun_iff_succ (· ~[r] ·)).mpr x.step h

Depends on / 依赖: Fin.liftFun_iff_succ, liftFun_iff_succ, x.step
-/
lemma rel_of_lt [r.IsTrans] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i < j) :
    x i ~[r] x j :=
  (Fin.liftFun_iff_succ (· ~[r] ·)).mpr x.step h

/--
lemma `rel_or_eq_of_le` / 引理 `rel_or_eq_of_le`

English:
lemma rel_or_eq_of_le
  given: [r.IsTrans] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i <= j)
  proof: (Fin.lt_or_eq_of_le h).imp (x.rel_of_lt ·) (by rw [·])

中文:
引理 rel_or_eq_of_le
  条件: [r.是Trans] (x : RelSeries r) {i j : 有限集 (x.length + 1)} (h : i <= j)
  证明: (Fin.lt_or_eq_of_le h).imp (x.rel_of_lt ·) (by rw [·])

Depends on / 依赖: Fin.lt_or_eq_of_le, lt_or_eq_of_le, rel_of_lt, x.rel_of_lt
-/
lemma rel_or_eq_of_le [r.IsTrans] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i <= j) :
    x i ~[r] x j ∨ x i = x j :=
  (Fin.lt_or_eq_of_le h).imp (x.rel_of_lt ·) (by rw [·])

/--
Given two relations `r, s` on `α` such that `r ≤ s`, any relation series of `r` induces a relation
series of `s`
-/
@[simps!]
/--
Definition of `ofLE` / `ofLE` 的定义

English:
definition ofLE
  signature: (x : RelSeries r) {s : SetRel α α} (h : r <= s)
  body: x.length
  toFun := x
step _ := h x.step _

中文:
定义 ofLE
  签名: (x : RelSeries r) {s : SetRel α α} (h : r <= s)
  定义体: x.length
  toFun := x
step _ := h x.step _

Depends on / 依赖: length, x.length
-/
def ofLE (x : RelSeries r) {s : SetRel α α} (h : r <= s) : RelSeries s where
  length := x.length
  toFun := x
step _ := h x.step _

/--
lemma `coe_ofLE` / 引理 `coe_ofLE`

English:
lemma coe_ofLE
  given: (x : RelSeries r) {s : SetRel α α} (h : r <= s)
  proof: rfl

中文:
引理 coe_ofLE
  条件: (x : RelSeries r) {s : SetRel α α} (h : r <= s)
  证明: rfl
-/
lemma coe_ofLE (x : RelSeries r) {s : SetRel α α} (h : r <= s) :
    (x.ofLE h : _ -> _) = x := rfl

/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: (x : RelSeries r)
  body: List.ofFn x

@[simp]

中文:
定义 toList
  签名: (x : RelSeries r)
  定义体: List.ofFn x

@[simp]

Depends on / 依赖: List.ofFn
-/
def toList (x : RelSeries r) : List α := List.ofFn x

@[simp]
/--
lemma `length_toList` / 引理 `length_toList`

English:
lemma length_toList
  given: (x : RelSeries r)
  statement: x.toList.length = x.length + 1
  proof: List.length_ofFn

@[simp]

中文:
引理 length_toList
  条件: (x : RelSeries r)
  结论: x.toList.length = x.length + 1
  证明: List.length_ofFn

@[simp]

Depends on / 依赖: List.length_ofFn, length_ofFn
-/
lemma length_toList (x : RelSeries r) : x.toList.length = x.length + 1 :=
  List.length_ofFn

@[simp]
/--
lemma `toList_singleton` / 引理 `toList_singleton`

English:
lemma toList_singleton
  given: (x : α)
  statement: (singleton r x).toList = [x]
  proof: by simp [toList, singleton]

中文:
引理 toList_singleton
  条件: (x : α)
  结论: (singleton r x).toList = [x]
  证明: by simp [toList, singleton]

Depends on / 依赖: singleton, toList
-/
lemma toList_singleton (x : α) : (singleton r x).toList = [x] := by simp [toList, singleton]

/--
lemma `isChain_toList` / 引理 `isChain_toList`

English:
lemma isChain_toList
  given: (x : RelSeries r)
  statement: x.toList.IsChain (· ~[r] ·)
  proof: by
  simp_rw [List.isChain_iff_getElem, length_toList, add_lt_add_iff_right]
  intro i h
  convert! x.step ⟨i, by simpa [toList] using h⟩ <;> apply List.get_ofFn

中文:
引理 isChain_toList
  条件: (x : RelSeries r)
  结论: x.toList.IsChain (· ~[r] ·)
  证明: by
  simp_rw [List.isChain_iff_getElem, length_toList, add_lt_add_iff_right]
  intro i h
  convert! x.step ⟨i, by simpa [toList] using h⟩ <;> apply List.get_ofFn

Depends on / 依赖: List.get_ofFn, List.isChain_iff_getElem, add_lt_add_iff_right, convert, get_ofFn, isChain_iff_getElem, length_toList, simp_rw, toList, x.step
-/
lemma isChain_toList (x : RelSeries r) : x.toList.IsChain (· ~[r] ·) := by
  simp_rw [List.isChain_iff_getElem, length_toList, add_lt_add_iff_right]
  intro i h
  convert! x.step ⟨i, by simpa [toList] using h⟩ <;> apply List.get_ofFn

/--
lemma `toList_ne_nil` / 引理 `toList_ne_nil`

English:
lemma toList_ne_nil
  given: (x : RelSeries r)
  statement: x.toList != []
  proof: fun m =>
List.eq_nil_iff_forall_not_mem.mp m (x 0) List.mem_ofFn.mpr ⟨_, rfl⟩

中文:
引理 toList_ne_nil
  条件: (x : RelSeries r)
  结论: x.toList != []
  证明: fun m =>
List.eq_nil_iff_forall_not_mem.mp m (x 0) List.mem_ofFn.mpr ⟨_, rfl⟩
-/
lemma toList_ne_nil (x : RelSeries r) : x.toList != [] := fun m =>
List.eq_nil_iff_forall_not_mem.mp m (x 0) List.mem_ofFn.mpr ⟨_, rfl⟩

/-- Every nonempty list satisfying the chain condition gives a relation series -/
@[simps]
/--
Definition of `fromListIsChain` / `fromListIsChain` 的定义

English:
definition fromListIsChain
  signature: (x : List α) (x_ne_nil : x != []) (hx : x.IsChain (· ~[r] ·))
  body: x.length - 1
  toFun i := x[Fin.cast (Nat.succ_pred_eq_of_pos <| List.length_pos_iff.mpr x_ne_nil) i]
  step i := List.isChain_iff_getElem.mp hx i _

中文:
定义 fromListIsChain
  签名: (x : 列表 α) (x_ne_nil : x != []) (hx : x.IsChain (· ~[r] ·))
  定义体: x.length - 1
  toFun i := x[Fin.cast (Nat.succ_pred_eq_of_pos <| List.length_pos_iff.mpr x_ne_nil) i]
  step i := List.isChain_iff_getElem.mp hx i _

Depends on / 依赖: length, x.length
-/
def fromListIsChain (x : List α) (x_ne_nil : x != []) (hx : x.IsChain (· ~[r] ·)) : RelSeries r where
  length := x.length - 1
  toFun i := x[Fin.cast (Nat.succ_pred_eq_of_pos <| List.length_pos_iff.mpr x_ne_nil) i]
  step i := List.isChain_iff_getElem.mp hx i _

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Equiv` / `Equiv` 的定义

English:
definition Equiv
  signature: : RelSeries r ≃ {x : List α | x != [] ∧ x.IsChain (· ~[r] ·)} where
  body: ⟨_, x.toList_ne_nil, x.isChain_toList⟩
  invFun x := fromListIsChain _ x.2.1 x.2.2
left_inv x := ext (by simp [toList]) by ext; dsimp; apply List.get_ofFn
  right_inv x := by
    refine Subtype.ext (List.ext_get ?_ fun n hn1 _ => by dsimp; apply List.get_ofFn)
have := Nat.succ_pred_eq_of_pos List.length_pos_iff.mpr x.2.1
    simp_all [toList]

中文:
定义 等价
  签名: : RelSeries r ≃ {x : 列表 α | x != [] ∧ x.IsChain (· ~[r] ·)} where
  定义体: ⟨_, x.toList_ne_nil, x.isChain_toList⟩
  invFun x := fromListIsChain _ x.2.1 x.2.2
left_inv x := ext (by simp [toList]) by ext; dsimp; apply List.get_ofFn
  right_inv x := by
    refine Subtype.ext (List.ext_get ?_ fun n hn1 _ => by dsimp; apply List.get_ofFn)
have := Nat.succ_pred_eq_of_pos List.length_pos_iff.mpr x.2.1
    simp_all [toList]
-/
protected def Equiv : RelSeries r ≃ {x : List α | x != [] ∧ x.IsChain (· ~[r] ·)} where
  toFun x := ⟨_, x.toList_ne_nil, x.isChain_toList⟩
  invFun x := fromListIsChain _ x.2.1 x.2.2
left_inv x := ext (by simp [toList]) by ext; dsimp; apply List.get_ofFn
  right_inv x := by
    refine Subtype.ext (List.ext_get ?_ fun n hn1 _ => by dsimp; apply List.get_ofFn)
have := Nat.succ_pred_eq_of_pos List.length_pos_iff.mpr x.2.1
    simp_all [toList]

/--
lemma `toList_injective` / 引理 `toList_injective`

English:
lemma toList_injective
  statement: Function.Injective (RelSeries.toList (r := r))
  proof: fun _ _ h => (RelSeries.Equiv).injective Subtype.ext h

中文:
引理 toList_injective
  结论: 函数.单射 (RelSeries.toList (r := r))
  证明: fun _ _ h => (RelSeries.Equiv).injective Subtype.ext h

Depends on / 依赖: Pi.isUnit_iff.mpr, isUnit_iff, map_units
-/
lemma toList_injective : Function.Injective (RelSeries.toList (r := r)) :=
fun _ _ h => (RelSeries.Equiv).injective Subtype.ext h

-- TODO : build a similar bijection between `RelSeries α` and `Quiver.Path`

end RelSeries

namespace SetRel

/-- A relation `r` is said to be finite dimensional iff there is a relation series of `r` with the
  maximum length. -/
@[mk_iff]
/--
Definition of `FiniteDimensional` / `FiniteDimensional` 的定义

English:
class FiniteDimensional
  parameters: : Prop where
  axioms and operations (1):
    - exists_longest_relSeries : exists x : RelSeries r, forall y : RelSeries r, y.length <= x.length

中文:
类 有限维
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_longest_relSeries : 存在 x : RelSeries r, 对任意 y : RelSeries r, y.length <= x.length
-/
class FiniteDimensional : Prop where
  /-- A relation `r` is said to be finite dimensional iff there is a relation series of `r` with the
  maximum length. -/
  exists_longest_relSeries : exists x : RelSeries r, forall y : RelSeries r, y.length <= x.length

/-- A relation `r` is said to be infinite dimensional iff there exists relation series of arbitrary
  length. -/
@[mk_iff]
/--
Definition of `InfiniteDimensional` / `InfiniteDimensional` 的定义

English:
class InfiniteDimensional
  parameters: : Prop where
  axioms and operations (1):
    - exists_relSeries_with_length : forall n : Nat, exists x : RelSeries r, x.length = n

中文:
类 无限维
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_relSeries_with_length : 对任意 n : 自然数, 存在 x : RelSeries r, x.length = n
-/
class InfiniteDimensional : Prop where
  /-- A relation `r` is said to be infinite dimensional iff there exists relation series of
  arbitrary length. -/
  exists_relSeries_with_length : forall n : Nat, exists x : RelSeries r, x.length = n

end SetRel

namespace RelSeries

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def longestOf [r.FiniteDimensional]
  body: SetRel.FiniteDimensional.exists_longest_relSeries.choose

中文:
定义 noncomputable
  签名: def longestOf [r.有限维]
  定义体: SetRel.FiniteDimensional.exists_longest_relSeries.choose
-/
protected noncomputable def longestOf [r.FiniteDimensional] : RelSeries r :=
  SetRel.FiniteDimensional.exists_longest_relSeries.choose

/--
lemma `length_le_length_longestOf` / 引理 `length_le_length_longestOf`

English:
lemma length_le_length_longestOf
  given: [r.FiniteDimensional] (x : RelSeries r)
  proof: SetRel.FiniteDimensional.exists_longest_relSeries.choose_spec _

中文:
引理 length_le_length_longestOf
  条件: [r.有限维] (x : RelSeries r)
  证明: SetRel.FiniteDimensional.exists_longest_relSeries.choose_spec _

Depends on / 依赖: FiniteDimensional, SetRel, SetRel.FiniteDimensional.exists_longest_relSeries.choose_spec, choose_spec, exists_longest_relSeries
-/
lemma length_le_length_longestOf [r.FiniteDimensional] (x : RelSeries r) :
    x.length <= (RelSeries.longestOf r).length :=
  SetRel.FiniteDimensional.exists_longest_relSeries.choose_spec _

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def withLength [r.InfiniteDimensional] (n : Nat)
  body: (SetRel.InfiniteDimensional.exists_relSeries_with_length n).choose

中文:
定义 noncomputable
  签名: def withLength [r.无限维] (n : 自然数)
  定义体: (SetRel.InfiniteDimensional.exists_relSeries_with_length n).choose
-/
protected noncomputable def withLength [r.InfiniteDimensional] (n : Nat) : RelSeries r :=
  (SetRel.InfiniteDimensional.exists_relSeries_with_length n).choose

/--
lemma `length_withLength` / 引理 `length_withLength`

English:
lemma length_withLength
  given: [r.InfiniteDimensional] (n : Nat)
  proof: (SetRel.InfiniteDimensional.exists_relSeries_with_length n).choose_spec

中文:
引理 length_withLength
  条件: [r.无限维] (n : 自然数)
  证明: (SetRel.InfiniteDimensional.exists_relSeries_with_length n).choose_spec
-/
@[simp] lemma length_withLength [r.InfiniteDimensional] (n : Nat) :
    (RelSeries.withLength r n).length = n :=
  (SetRel.InfiniteDimensional.exists_relSeries_with_length n).choose_spec

section
variable {r} {s : RelSeries r} {x : α}

/--
lemma `nonempty_of_infiniteDimensional` / 引理 `nonempty_of_infiniteDimensional`

English:
lemma nonempty_of_infiniteDimensional
  given: [r.InfiniteDimensional]
  statement: Nonempty α
  proof: ⟨RelSeries.withLength r 0 0⟩

中文:
引理 nonempty_of_infiniteDimensional
  条件: [r.无限维]
  结论: 非空 α
  证明: ⟨RelSeries.withLength r 0 0⟩

Depends on / 依赖: RelSeries, RelSeries.withLength, withLength
-/
lemma nonempty_of_infiniteDimensional [r.InfiniteDimensional] : Nonempty α :=
  ⟨RelSeries.withLength r 0 0⟩

/--
lemma `nonempty_of_finiteDimensional` / 引理 `nonempty_of_finiteDimensional`

English:
lemma nonempty_of_finiteDimensional
  given: [r.FiniteDimensional]
  statement: Nonempty α
  proof: by
  obtain ⟨p, _⟩ := (r.finiteDimensional_iff).mp ‹_›
  exact ⟨p 0⟩

中文:
引理 nonempty_of_finiteDimensional
  条件: [r.有限维]
  结论: 非空 α
  证明: by
  obtain ⟨p, _⟩ := (r.finiteDimensional_iff).mp ‹_›
  exact ⟨p 0⟩

Depends on / 依赖: finiteDimensional_iff, r.finiteDimensional_iff
-/
lemma nonempty_of_finiteDimensional [r.FiniteDimensional] : Nonempty α := by
  obtain ⟨p, _⟩ := (r.finiteDimensional_iff).mp ‹_›
  exact ⟨p 0⟩

/--
Instance `membership` / 实例 `membership`

English:
instance membership
  signature: : Membership α (RelSeries r)
  body: ⟨Function.swap (· in Set.range ·)⟩

中文:
实例 membership
  签名: : Membership α (RelSeries r)
  定义体: ⟨Function.swap (· in Set.range ·)⟩

Depends on / 依赖: Function, Function.swap, Set.range
-/
instance membership : Membership α (RelSeries r) :=
  ⟨Function.swap (· in Set.range ·)⟩

/--
theorem `mem_def` / 定理 `mem_def`

English:
theorem mem_def
  statement: x in s ↔ x in Set.range s
  proof: Iff.rfl

中文:
定理 mem_def
  结论: x in s ↔ x in 集合.range s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_def : x in s ↔ x in Set.range s := Iff.rfl

/--
theorem `mem_toList` / 定理 `mem_toList`

English:
theorem mem_toList
  statement: x in s.toList ↔ x in s
  proof: by
  rw [RelSeries.toList]; rw [List.mem_ofFn']; rw [RelSeries.mem_def]

中文:
定理 mem_toList
  结论: x in s.toList ↔ x in s
  证明: by
  rw [RelSeries.toList]; rw [List.mem_ofFn']; rw [RelSeries.mem_def]
-/
@[simp] theorem mem_toList : x in s.toList ↔ x in s := by
  rw [RelSeries.toList]; rw [List.mem_ofFn']; rw [RelSeries.mem_def]

/--
theorem `subsingleton_of_length_eq_zero` / 定理 `subsingleton_of_length_eq_zero`

English:
theorem subsingleton_of_length_eq_zero
  given: (hs : s.length = 0)
  statement: {x | x in s}.Subsingleton
  proof: by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  congr!
.injective Subsingleton.elim (α := Fin 1) _ _ exact finCongr (by rw [hs, zero_add])

中文:
定理 subsingleton_of_length_eq_zero
  条件: (hs : s.length = 0)
  结论: {x | x in s}.子单例
  证明: by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  congr!
.injective Subsingleton.elim (α := Fin 1) _ _ exact finCongr (by rw [hs, zero_add])

Depends on / 依赖: Subsingleton, Subsingleton.elim, finCongr, injective, zero_add
-/
theorem subsingleton_of_length_eq_zero (hs : s.length = 0) : {x | x in s}.Subsingleton := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  congr!
.injective Subsingleton.elim (α := Fin 1) _ _ exact finCongr (by rw [hs, zero_add])

/--
theorem `length_ne_zero_of_nontrivial` / 定理 `length_ne_zero_of_nontrivial`

English:
theorem length_ne_zero_of_nontrivial
  given: (h : {x | x in s}.Nontrivial)
  statement: s.length != 0
  proof: fun hs => h.not_subsingleton subsingleton_of_length_eq_zero hs

中文:
定理 length_ne_zero_of_nontrivial
  条件: (h : {x | x in s}.非平凡)
  结论: s.length != 0
  证明: fun hs => h.not_subsingleton subsingleton_of_length_eq_zero hs

Depends on / 依赖: h.not_subsingleton, not_subsingleton, subsingleton_of_length_eq_zero
-/
theorem length_ne_zero_of_nontrivial (h : {x | x in s}.Nontrivial) : s.length != 0 :=
fun hs => h.not_subsingleton subsingleton_of_length_eq_zero hs

/--
theorem `length_pos_of_nontrivial` / 定理 `length_pos_of_nontrivial`

English:
theorem length_pos_of_nontrivial
  given: (h : {x | x in s}.Nontrivial)
  statement: 0 < s.length
  proof: Nat.pos_iff_ne_zero.mpr length_ne_zero_of_nontrivial h

中文:
定理 length_pos_of_nontrivial
  条件: (h : {x | x in s}.非平凡)
  结论: 0 < s.length
  证明: Nat.pos_iff_ne_zero.mpr length_ne_zero_of_nontrivial h

Depends on / 依赖: Nat.pos_iff_ne_zero.mpr, length_ne_zero_of_nontrivial, pos_iff_ne_zero
-/
theorem length_pos_of_nontrivial (h : {x | x in s}.Nontrivial) : 0 < s.length :=
Nat.pos_iff_ne_zero.mpr length_ne_zero_of_nontrivial h

/--
theorem `length_ne_zero` / 定理 `length_ne_zero`

English:
theorem length_ne_zero
  given: [r.IsIrrefl]
  statement: s.length != 0 ↔ {x | x in s}.Nontrivial
  proof: by
  refine ⟨fun h => ⟨s 0, by simp [mem_def], s 1, by simp [mem_def],
    fun rid => r.irrefl (s 0) ?_⟩, length_ne_zero_of_nontrivial⟩
  nth_rw 2 [rid]
  convert! s.step ⟨0, by lia⟩
  ext
  simpa [Nat.pos_iff_ne_zero]

中文:
定理 length_ne_zero
  条件: [r.IsIrrefl]
  结论: s.length != 0 ↔ {x | x in s}.非平凡
  证明: by
  refine ⟨fun h => ⟨s 0, by simp [mem_def], s 1, by simp [mem_def],
    fun rid => r.irrefl (s 0) ?_⟩, length_ne_zero_of_nontrivial⟩
  nth_rw 2 [rid]
  convert! s.step ⟨0, by lia⟩
  ext
  simpa [Nat.pos_iff_ne_zero]

Depends on / 依赖: Nat.pos_iff_ne_zero, convert, irrefl, length_ne_zero_of_nontrivial, mem_def, nth_rw, pos_iff_ne_zero, r.irrefl, s.step
-/
theorem length_ne_zero [r.IsIrrefl] : s.length != 0 ↔ {x | x in s}.Nontrivial := by
  refine ⟨fun h => ⟨s 0, by simp [mem_def], s 1, by simp [mem_def],
    fun rid => r.irrefl (s 0) ?_⟩, length_ne_zero_of_nontrivial⟩
  nth_rw 2 [rid]
  convert! s.step ⟨0, by lia⟩
  ext
  simpa [Nat.pos_iff_ne_zero]

/--
theorem `length_pos` / 定理 `length_pos`

English:
theorem length_pos
  given: [r.IsIrrefl]
  statement: 0 < s.length ↔ {x | x in s}.Nontrivial
  proof: Nat.pos_iff_ne_zero.trans length_ne_zero

中文:
定理 length_pos
  条件: [r.IsIrrefl]
  结论: 0 < s.length ↔ {x | x in s}.非平凡
  证明: Nat.pos_iff_ne_zero.trans length_ne_zero

Depends on / 依赖: Nat.pos_iff_ne_zero.trans, length_ne_zero, pos_iff_ne_zero
-/
theorem length_pos [r.IsIrrefl] : 0 < s.length ↔ {x | x in s}.Nontrivial :=
  Nat.pos_iff_ne_zero.trans length_ne_zero

/--
lemma `length_eq_zero` / 引理 `length_eq_zero`

English:
lemma length_eq_zero
  given: [r.IsIrrefl]
  statement: s.length = 0 ↔ {x | x in s}.Subsingleton
  proof: by
  rw [← not_ne_iff]; rw [length_ne_zero]; rw [Set.not_nontrivial_iff]

中文:
引理 length_eq_zero
  条件: [r.IsIrrefl]
  结论: s.length = 0 ↔ {x | x in s}.子单例
  证明: by
  rw [← not_ne_iff]; rw [length_ne_zero]; rw [Set.not_nontrivial_iff]

Depends on / 依赖: Set.not_nontrivial_iff, length_ne_zero, not_ne_iff, not_nontrivial_iff
-/
lemma length_eq_zero [r.IsIrrefl] : s.length = 0 ↔ {x | x in s}.Subsingleton := by
  rw [← not_ne_iff]; rw [length_ne_zero]; rw [Set.not_nontrivial_iff]

/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: (x : RelSeries r)
  body: x 0

中文:
定义 head
  签名: (x : RelSeries r)
  定义体: x 0
-/
def head (x : RelSeries r) : α := x 0

/--
Definition of `last` / `last` 的定义

English:
definition last
  signature: (x : RelSeries r)
  body: x Fin.last _

中文:
定义 last
  签名: (x : RelSeries r)
  定义体: x Fin.last _

Depends on / 依赖: Fin.last
-/
def last (x : RelSeries r) : α := x Fin.last _

/--
lemma `apply_zero` / 引理 `apply_zero`

English:
lemma apply_zero
  given: (p : RelSeries r)
  statement: p 0 = p.head
  proof: rfl

中文:
引理 apply_zero
  条件: (p : RelSeries r)
  结论: p 0 = p.head
  证明: rfl
-/
lemma apply_zero (p : RelSeries r) : p 0 = p.head := rfl

/--
lemma `apply_last` / 引理 `apply_last`

English:
lemma apply_last
  given: (x : RelSeries r)
  statement: x (Fin.last <| x.length) = x.last
  proof: rfl

中文:
引理 apply_last
  条件: (x : RelSeries r)
  结论: x (有限集.last <| x.length) = x.last
  证明: rfl

Depends on / 依赖: IsLocalization, IsLocalization.isNoetherianRing, isNoetherianRing
-/
lemma apply_last (x : RelSeries r) : x (Fin.last <| x.length) = x.last := rfl

/--
lemma `head_mem` / 引理 `head_mem`

English:
lemma head_mem
  given: (x : RelSeries r)
  statement: x.head in x
  proof: ⟨_, rfl⟩

中文:
引理 head_mem
  条件: (x : RelSeries r)
  结论: x.head in x
  证明: ⟨_, rfl⟩
-/
lemma head_mem (x : RelSeries r) : x.head in x := ⟨_, rfl⟩

/--
lemma `last_mem` / 引理 `last_mem`

English:
lemma last_mem
  given: (x : RelSeries r)
  statement: x.last in x
  proof: ⟨_, rfl⟩

@[simp]

中文:
引理 last_mem
  条件: (x : RelSeries r)
  结论: x.last in x
  证明: ⟨_, rfl⟩

@[simp]
-/
lemma last_mem (x : RelSeries r) : x.last in x := ⟨_, rfl⟩

@[simp]
/--
lemma `head_singleton` / 引理 `head_singleton`

English:
lemma head_singleton
  given: {r : SetRel α α} (x : α)
  statement: (singleton r x).head = x
  proof: by
  simp [singleton, head]

@[simp]

中文:
引理 head_singleton
  条件: {r : SetRel α α} (x : α)
  结论: (singleton r x).head = x
  证明: by
  simp [singleton, head]

@[simp]

Depends on / 依赖: singleton
-/
lemma head_singleton {r : SetRel α α} (x : α) : (singleton r x).head = x := by
  simp [singleton, head]

@[simp]
/--
lemma `last_singleton` / 引理 `last_singleton`

English:
lemma last_singleton
  given: {r : SetRel α α} (x : α)
  statement: (singleton r x).last = x
  proof: by
  simp [singleton, last]

@[simp]

中文:
引理 last_singleton
  条件: {r : SetRel α α} (x : α)
  结论: (singleton r x).last = x
  证明: by
  simp [singleton, last]

@[simp]

Depends on / 依赖: singleton
-/
lemma last_singleton {r : SetRel α α} (x : α) : (singleton r x).last = x := by
  simp [singleton, last]

@[simp]
/--
lemma `head_toList` / 引理 `head_toList`

English:
lemma head_toList
  given: (p : RelSeries r)
  statement: p.toList.head p.toList_ne_nil = p.head
  proof: by
  simp [toList, apply_zero]

@[simp]

中文:
引理 head_toList
  条件: (p : RelSeries r)
  结论: p.toList.head p.toList_ne_nil = p.head
  证明: by
  simp [toList, apply_zero]

@[simp]

Depends on / 依赖: apply_zero, toList
-/
lemma head_toList (p : RelSeries r) : p.toList.head p.toList_ne_nil = p.head := by
  simp [toList, apply_zero]

@[simp]
/--
lemma `toList_getElem` / 引理 `toList_getElem`

English:
lemma toList_getElem
  given: (p : RelSeries r) {i : Nat} (hi : i < p.toList.length)
  proof: by
  simp only [toList, List.getElem_ofFn]

中文:
引理 toList_getElem
  条件: (p : RelSeries r) {i : 自然数} (hi : i < p.toList.length)
  证明: by
  simp only [toList, List.getElem_ofFn]

Depends on / 依赖: List.getElem_ofFn, getElem_ofFn, toList
-/
lemma toList_getElem (p : RelSeries r) {i : Nat} (hi : i < p.toList.length) :
    p.toList[(i : Nat)] = p ⟨i, by simpa using hi⟩ := by
  simp only [toList, List.getElem_ofFn]

/--
lemma `toList_getElem_zero_eq_head` / 引理 `toList_getElem_zero_eq_head`

English:
lemma toList_getElem_zero_eq_head
  given: (p : RelSeries r)
  statement: p.toList[0] = p.head
  proof: p.toList_getElem _

@[simp]

中文:
引理 toList_getElem_zero_eq_head
  条件: (p : RelSeries r)
  结论: p.toList[0] = p.head
  证明: p.toList_getElem _

@[simp]

Depends on / 依赖: p.toList_getElem, toList_getElem
-/
lemma toList_getElem_zero_eq_head (p : RelSeries r) : p.toList[0] = p.head :=
  p.toList_getElem _

@[simp]
/--
lemma `toList_fromListIsChain` / 引理 `toList_fromListIsChain`

English:
lemma toList_fromListIsChain
  given: (l : List α) (l_ne_nil : l != []) (hl : l.IsChain (· ~[r] ·))
  proof: Subtype.ext_iff.mp RelSeries.Equiv.right_inv ⟨l, ⟨l_ne_nil, hl⟩⟩

中文:
引理 toList_fromListIsChain
  条件: (l : 列表 α) (l_ne_nil : l != []) (hl : l.IsChain (· ~[r] ·))
  证明: Subtype.ext_iff.mp RelSeries.Equiv.right_inv ⟨l, ⟨l_ne_nil, hl⟩⟩

Depends on / 依赖: RelSeries, RelSeries.Equiv.right_inv, Subtype, Subtype.ext_iff.mp, ext_iff, l_ne_nil, right_inv
-/
lemma toList_fromListIsChain (l : List α) (l_ne_nil : l != []) (hl : l.IsChain (· ~[r] ·)) :
    (fromListIsChain l l_ne_nil hl).toList = l :=
Subtype.ext_iff.mp RelSeries.Equiv.right_inv ⟨l, ⟨l_ne_nil, hl⟩⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `head_fromListIsChain` / 引理 `head_fromListIsChain`

English:
lemma head_fromListIsChain
  given: (l : List α) (l_ne_nil : l != []) (hl : l.IsChain (· ~[r] ·))
  proof: by
  simp [← apply_zero, List.getElem_zero_eq_head]

@[simp]

中文:
引理 head_fromListIsChain
  条件: (l : 列表 α) (l_ne_nil : l != []) (hl : l.IsChain (· ~[r] ·))
  证明: by
  simp [← apply_zero, List.getElem_zero_eq_head]

@[simp]

Depends on / 依赖: List.getElem_zero_eq_head, apply_zero, getElem_zero_eq_head
-/
lemma head_fromListIsChain (l : List α) (l_ne_nil : l != []) (hl : l.IsChain (· ~[r] ·)) :
    (fromListIsChain l l_ne_nil hl).head = l.head l_ne_nil := by
  simp [← apply_zero, List.getElem_zero_eq_head]

@[simp]
/--
lemma `getLast_toList` / 引理 `getLast_toList`

English:
lemma getLast_toList
  given: (p : RelSeries r)
  statement: p.toList.getLast (by simp [toList]) = p.last
  proof: by
  grind [length_toList, last, Fin.last, toList_getElem]

中文:
引理 getLast_toList
  条件: (p : RelSeries r)
  结论: p.toList.getLast (by simp [toList]) = p.last
  证明: by
  grind [length_toList, last, Fin.last, toList_getElem]

Depends on / 依赖: Fin.last, length_toList, toList_getElem
-/
lemma getLast_toList (p : RelSeries r) : p.toList.getLast (by simp [toList]) = p.last := by
  grind [length_toList, last, Fin.last, toList_getElem]

end

variable {r s}

/--
If `a₀ -r→ a₁ -r→ ... -r→ aₙ` and `b₀ -r→ b₁ -r→ ... -r→ bₘ` are two strict series
such that `r aₙ b₀`, then there is a chain of length `n + m + 1` given by
`a₀ -r→ a₁ -r→ ... -r→ aₙ -r→ b₀ -r→ b₁ -r→ ... -r→ bₘ`.
-/
@[simps]
/--
Definition of `append` / `append` 的定义

English:
definition append
  signature: (p q : RelSeries r) (connect : p.last ~[r] q.head)
  body: p.length + q.length + 1
  toFun := Fin.append p q ∘ Fin.cast (by lia)
  step i := by
    obtain hi | rfl | hi :=
      lt_trichotomy i (Fin.castLE (by lia) (Fin.last _ : Fin (p.length + 1)))
    · convert! p.step ⟨i.1, hi⟩ <;> convert! Fin.append_left p q _ <;> rfl
    · convert! connect
      · convert! Fin.append_left p q _
      · convert! Fin.append_right p q _; rfl
    · set x := _; set y := _
      change Fin.append p q x ~[r] Fin.append p q y
have hx : x = Fin.natAdd _ ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi
i.2.trans by lia⟩ := by
        ext; dsimp [x, y]; rw [Nat.add_sub_cancel']; exact hi
      have hy : y = Fin.natAdd _ ⟨i - p.length, Nat.sub_lt_left_of_lt_add (le_of_lt hi)
          (by exact i.2)⟩ := by
        ext
        dsimp
        conv_rhs => rw [Nat.add_comm p.length 1, add_assoc,
Nat.add_sub_cancel' le_of_lt (show p.length < i.1 from hi), add_comm]
        rfl
      rw [hx]; rw [Fin.append_right]; rw [hy]; rw [Fin.append_right]
convert! q.step ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi by lia⟩
      rw [Fin.succ_mk]; rw [Nat.sub_eq_iff_eq_add (le_of_lt hi : p.length <= i)]; rw [Nat.add_assoc _ 1]; rw [add_comm 1]; rw [Nat.sub_add_cancel]
      exact hi

中文:
定义 append
  签名: (p q : RelSeries r) (connect : p.last ~[r] q.head)
  定义体: p.length + q.length + 1
  toFun := Fin.append p q ∘ Fin.cast (by lia)
  step i := by
    obtain hi | rfl | hi :=
      lt_trichotomy i (Fin.castLE (by lia) (Fin.last _ : Fin (p.length + 1)))
    · convert! p.step ⟨i.1, hi⟩ <;> convert! Fin.append_left p q _ <;> rfl
    · convert! connect
      · convert! Fin.append_left p q _
      · convert! Fin.append_right p q _; rfl
    · set x := _; set y := _
      change Fin.append p q x ~[r] Fin.append p q y
have hx : x = Fin.natAdd _ ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi
i.2.trans by lia⟩ := by
        ext; dsimp [x, y]; rw [Nat.add_sub_cancel']; exact hi
      have hy : y = Fin.natAdd _ ⟨i - p.length, Nat.sub_lt_left_of_lt_add (le_of_lt hi)
          (by exact i.2)⟩ := by
        ext
        dsimp
        conv_rhs => rw [Nat.add_comm p.length 1, add_assoc,
Nat.add_sub_cancel' le_of_lt (show p.length < i.1 from hi), add_comm]
        rfl
      rw [hx]; rw [Fin.append_right]; rw [hy]; rw [Fin.append_right]
convert! q.step ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi by lia⟩
      rw [Fin.succ_mk]; rw [Nat.sub_eq_iff_eq_add (le_of_lt hi : p.length <= i)]; rw [Nat.add_assoc _ 1]; rw [add_comm 1]; rw [Nat.sub_add_cancel]
      exact hi

Depends on / 依赖: length, p.length, q.length
-/
def append (p q : RelSeries r) (connect : p.last ~[r] q.head) : RelSeries r where
  length := p.length + q.length + 1
  toFun := Fin.append p q ∘ Fin.cast (by lia)
  step i := by
    obtain hi | rfl | hi :=
      lt_trichotomy i (Fin.castLE (by lia) (Fin.last _ : Fin (p.length + 1)))
    · convert! p.step ⟨i.1, hi⟩ <;> convert! Fin.append_left p q _ <;> rfl
    · convert! connect
      · convert! Fin.append_left p q _
      · convert! Fin.append_right p q _; rfl
    · set x := _; set y := _
      change Fin.append p q x ~[r] Fin.append p q y
have hx : x = Fin.natAdd _ ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi
i.2.trans by lia⟩ := by
        ext; dsimp [x, y]; rw [Nat.add_sub_cancel']; exact hi
      have hy : y = Fin.natAdd _ ⟨i - p.length, Nat.sub_lt_left_of_lt_add (le_of_lt hi)
          (by exact i.2)⟩ := by
        ext
        dsimp
        conv_rhs => rw [Nat.add_comm p.length 1, add_assoc,
Nat.add_sub_cancel' le_of_lt (show p.length < i.1 from hi), add_comm]
        rfl
      rw [hx]; rw [Fin.append_right]; rw [hy]; rw [Fin.append_right]
convert! q.step ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi by lia⟩
      rw [Fin.succ_mk]; rw [Nat.sub_eq_iff_eq_add (le_of_lt hi : p.length <= i)]; rw [Nat.add_assoc _ 1]; rw [add_comm 1]; rw [Nat.sub_add_cancel]
      exact hi

set_option backward.defeqAttrib.useBackward true in
/--
lemma `append_apply_left` / 引理 `append_apply_left`

English:
lemma append_apply_left
  statement: (p q : RelSeries r) (connect : p.last ~[r] q.head)
  proof: by
  delta append
  simp only [Function.comp_apply]
  convert! Fin.append_left _ _ _

中文:
引理 append_apply_left
  结论: (p q : RelSeries r) (connect : p.last ~[r] q.head)
  证明: by
  delta append
  simp only [Function.comp_apply]
  convert! Fin.append_left _ _ _

Depends on / 依赖: Fin.append_left, Function, Function.comp_apply, append, append_left, comp_apply, convert
-/
lemma append_apply_left (p q : RelSeries r) (connect : p.last ~[r] q.head)
    (i : Fin (p.length + 1)) :
    p.append q connect
      ((i.castAdd (q.length + 1)).cast (by dsimp; lia) : Fin ((p.append q connect).length + 1))
        = p i := by
  delta append
  simp only [Function.comp_apply]
  convert! Fin.append_left _ _ _

set_option backward.defeqAttrib.useBackward true in
/--
lemma `append_apply_right` / 引理 `append_apply_right`

English:
lemma append_apply_right
  statement: (p q : RelSeries r) (connect : p.last ~[r] q.head)
  proof: Fin.append_right _ _ _

中文:
引理 append_apply_right
  结论: (p q : RelSeries r) (connect : p.last ~[r] q.head)
  证明: Fin.append_right _ _ _

Depends on / 依赖: Fin.append_right, append_right
-/
lemma append_apply_right (p q : RelSeries r) (connect : p.last ~[r] q.head)
    (i : Fin (q.length + 1)) :
    p.append q connect
      ((i.natAdd (p.length + 1)).cast (by dsimp; lia) : Fin ((p.append q connect).length + 1))
        = q i :=
  Fin.append_right _ _ _

/--
lemma `head_append` / 引理 `head_append`

English:
lemma head_append
  given: (p q : RelSeries r) (connect : p.last ~[r] q.head)
  proof: append_apply_left p q connect 0

中文:
引理 head_append
  条件: (p q : RelSeries r) (connect : p.last ~[r] q.head)
  证明: append_apply_left p q connect 0
-/
@[simp] lemma head_append (p q : RelSeries r) (connect : p.last ~[r] q.head) :
    (p.append q connect).head = p.head :=
  append_apply_left p q connect 0

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `last_append` / 引理 `last_append`

English:
lemma last_append
  given: (p q : RelSeries r) (connect : p.last ~[r] q.head)
  proof: by
  delta last
  convert! append_apply_right p q connect (Fin.last _)
  ext1
  dsimp
  lia

中文:
引理 last_append
  条件: (p q : RelSeries r) (connect : p.last ~[r] q.head)
  证明: by
  delta last
  convert! append_apply_right p q connect (Fin.last _)
  ext1
  dsimp
  lia

Depends on / 依赖: AtPrime, IsLocalization, IsLocalization.AtPrime.isLocalRing, Localization, P.primeCompl, isLocalRing, primeCompl
-/
@[simp] lemma last_append (p q : RelSeries r) (connect : p.last ~[r] q.head) :
    (p.append q connect).last = q.last := by
  delta last
  convert! append_apply_right p q connect (Fin.last _)
  ext1
  dsimp
  lia

set_option backward.isDefEq.respectTransparency false in
/--
lemma `append_assoc` / 引理 `append_assoc`

English:
lemma append_assoc
  given: (p q w : RelSeries r) (hpq : p.last ~[r] q.head) (hqw : q.last ~[r] w.head)
  proof: by
  ext
  · simp only [append_length, Nat.add_left_inj]
    lia
  · simp [append, Fin.append_assoc]

中文:
引理 append_assoc
  条件: (p q w : RelSeries r) (hpq : p.last ~[r] q.head) (hqw : q.last ~[r] w.head)
  证明: by
  ext
  · simp only [append_length, Nat.add_left_inj]
    lia
  · simp [append, Fin.append_assoc]

Depends on / 依赖: Fin.append_assoc, Nat.add_left_inj, P.primeCompl_le_nonZeroDivisors, add_left_inj, append, append_assoc, append_length, of_isLocalization, primeCompl_le_nonZeroDivisors
-/
lemma append_assoc (p q w : RelSeries r) (hpq : p.last ~[r] q.head) (hqw : q.last ~[r] w.head) :
    (p.append q hpq).append w (by simpa) = p.append (q.append w hqw) (by simpa) := by
  ext
  · simp only [append_length, Nat.add_left_inj]
    lia
  · simp [append, Fin.append_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `toList_append` / 引理 `toList_append`

English:
lemma toList_append
  given: (p q : RelSeries r) (connect : p.last ~[r] q.head)
  proof: by
  apply List.ext_getElem
  · simp; grind
  · simp [List.getElem_append, Fin.append, Fin.addCases]

中文:
引理 toList_append
  条件: (p q : RelSeries r) (connect : p.last ~[r] q.head)
  证明: by
  apply List.ext_getElem
  · simp; grind
  · simp [List.getElem_append, Fin.append, Fin.addCases]

Depends on / 依赖: Fin.addCases, Fin.append, List.ext_getElem, List.getElem_append, addCases, append, ext_getElem, getElem_append
-/
lemma toList_append (p q : RelSeries r) (connect : p.last ~[r] q.head) :
    (p.append q connect).toList = p.toList ++ q.toList := by
  apply List.ext_getElem
  · simp; grind
  · simp [List.getElem_append, Fin.append, Fin.addCases]
/--
For two types `α, β` and relation on them `r, s`, if `f : α → β` preserves relation `r`, then an
`r`-series can be pushed out to an `s`-series by
`a₀ -r→ a₁ -r→ ... -r→ aₙ ↦ f a₀ -s→ f a₁ -s→ ... -s→ f aₙ`
-/
@[simps length]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (p : RelSeries r) (f : r.Hom s)
  body: p.length
  toFun := f.1.comp p
  step := (f.2 <| p.step ·)

中文:
定义 map
  签名: (p : RelSeries r) (f : r.态射 s)
  定义体: p.length
  toFun := f.1.comp p
  step := (f.2 <| p.step ·)

Depends on / 依赖: AtPrime, IsLocalization, IsLocalization.AtPrime.faithfulSMul, faithfulSMul, length, p.length
-/
def map (p : RelSeries r) (f : r.Hom s) : RelSeries s where
  length := p.length
  toFun := f.1.comp p
  step := (f.2 <| p.step ·)

/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  given: (p : RelSeries r) (f : r.Hom s) (i : Fin (p.length + 1))
  proof: rfl

中文:
引理 map_apply
  条件: (p : RelSeries r) (f : r.态射 s) (i : 有限集 (p.length + 1))
  证明: rfl
-/
@[simp] lemma map_apply (p : RelSeries r) (f : r.Hom s) (i : Fin (p.length + 1)) :
    p.map f i = f (p i) := rfl

/--
lemma `head_map` / 引理 `head_map`

English:
lemma head_map
  given: (p : RelSeries r) (f : r.Hom s)
  statement: (p.map f).head = f p.head
  proof: rfl

中文:
引理 head_map
  条件: (p : RelSeries r) (f : r.态射 s)
  结论: (p.map f).head = f p.head
  证明: rfl
-/
@[simp] lemma head_map (p : RelSeries r) (f : r.Hom s) : (p.map f).head = f p.head := rfl

/--
lemma `last_map` / 引理 `last_map`

English:
lemma last_map
  given: (p : RelSeries r) (f : r.Hom s)
  statement: (p.map f).last = f p.last
  proof: rfl

中文:
引理 last_map
  条件: (p : RelSeries r) (f : r.态射 s)
  结论: (p.map f).last = f p.last
  证明: rfl
-/
@[simp] lemma last_map (p : RelSeries r) (f : r.Hom s) : (p.map f).last = f p.last := rfl

set_option backward.isDefEq.respectTransparency false in
/--
If `a₀ -r→ a₁ -r→ ... -r→ aₙ` is an `r`-series and `a` is such that
`aᵢ -r→ a -r→ a_ᵢ₊₁`, then
`a₀ -r→ a₁ -r→ ... -r→ aᵢ -r→ a -r→ aᵢ₊₁ -r→ ... -r→ aₙ`
is another `r`-series
-/
@[simps]
/--
Definition of `insertNth` / `insertNth` 的定义

English:
definition insertNth
  signature: (p : RelSeries r) (i : Fin p.length) (a : α)
  body: p.length + 1
  toFun := (Fin.castSucc i.succ).insertNth a p
  step m := by
    set x := _; set y := _; change x ~[r] y
    obtain hm | hm | hm := lt_trichotomy m.1 i.1
    · convert! p.step ⟨m, hm.trans i.2⟩
      · change Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · exact hm.trans (lt_add_one _)
        simp
      · change Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · change m.1 + 1 < i.1 + 1; rwa [add_lt_add_iff_right]
        simp; rfl
    · rw [show x = p m from show Fin.insertNth _ _ _ _ = _ by
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · change m.1 < i.1 + 1; exact hm ▸ lt_add_one _
        simp]
      convert! prev_connect
      · ext; exact hm
      · change Fin.insertNth _ _ _ _ = _
        rw [show m.succ = i.succ.castSucc by ext; change _ + 1 = _ + 1; rw [hm],
          Fin.insertNth_apply_same]
    · rw [Nat.lt_iff_add_one_le, le_iff_lt_or_eq] at hm
      obtain hm | hm := hm
      · convert! p.step ⟨m.1 - 1, Nat.sub_lt_right_of_lt_add (by lia) m.2⟩
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above (h := hm)]
          aesop
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap
          · exact hm.trans (lt_add_one _)
          simp only [Fin.pred_succ, eq_rec_constant, Fin.succ_mk]
          congr
exact Fin.ext Eq.symm Nat.succ_pred_eq_of_pos (lt_trans (Nat.zero_lt_succ _) hm)
      · convert! connect_next
        · change Fin.insertNth _ _ _ _ = _
          rw [show m.castSucc = i.succ.castSucc from Fin.ext hm.symm]; rw [Fin.insertNth_apply_same]
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap
          · change i.1 + 1 < m.1 + 1; lia
          simp only [Fin.pred_succ, eq_rec_constant]
          congr; ext; exact hm.symm

中文:
定义 insertNth
  签名: (p : RelSeries r) (i : 有限集 p.length) (a : α)
  定义体: p.length + 1
  toFun := (Fin.castSucc i.succ).insertNth a p
  step m := by
    set x := _; set y := _; change x ~[r] y
    obtain hm | hm | hm := lt_trichotomy m.1 i.1
    · convert! p.step ⟨m, hm.trans i.2⟩
      · change Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · exact hm.trans (lt_add_one _)
        simp
      · change Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · change m.1 + 1 < i.1 + 1; rwa [add_lt_add_iff_right]
        simp; rfl
    · rw [show x = p m from show Fin.insertNth _ _ _ _ = _ by
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · change m.1 < i.1 + 1; exact hm ▸ lt_add_one _
        simp]
      convert! prev_connect
      · ext; exact hm
      · change Fin.insertNth _ _ _ _ = _
        rw [show m.succ = i.succ.castSucc by ext; change _ + 1 = _ + 1; rw [hm],
          Fin.insertNth_apply_same]
    · rw [Nat.lt_iff_add_one_le, le_iff_lt_or_eq] at hm
      obtain hm | hm := hm
      · convert! p.step ⟨m.1 - 1, Nat.sub_lt_right_of_lt_add (by lia) m.2⟩
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above (h := hm)]
          aesop
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap
          · exact hm.trans (lt_add_one _)
          simp only [Fin.pred_succ, eq_rec_constant, Fin.succ_mk]
          congr
exact Fin.ext Eq.symm Nat.succ_pred_eq_of_pos (lt_trans (Nat.zero_lt_succ _) hm)
      · convert! connect_next
        · change Fin.insertNth _ _ _ _ = _
          rw [show m.castSucc = i.succ.castSucc from Fin.ext hm.symm]; rw [Fin.insertNth_apply_same]
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap
          · change i.1 + 1 < m.1 + 1; lia
          simp only [Fin.pred_succ, eq_rec_constant]
          congr; ext; exact hm.symm

Depends on / 依赖: length, p.length
-/
def insertNth (p : RelSeries r) (i : Fin p.length) (a : α)
    (prev_connect : p (Fin.castSucc i) ~[r] a) (connect_next : a ~[r] p i.succ) : RelSeries r where
  length := p.length + 1
  toFun := (Fin.castSucc i.succ).insertNth a p
  step m := by
    set x := _; set y := _; change x ~[r] y
    obtain hm | hm | hm := lt_trichotomy m.1 i.1
    · convert! p.step ⟨m, hm.trans i.2⟩
      · change Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · exact hm.trans (lt_add_one _)
        simp
      · change Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · change m.1 + 1 < i.1 + 1; rwa [add_lt_add_iff_right]
        simp; rfl
    · rw [show x = p m from show Fin.insertNth _ _ _ _ = _ by
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · change m.1 < i.1 + 1; exact hm ▸ lt_add_one _
        simp]
      convert! prev_connect
      · ext; exact hm
      · change Fin.insertNth _ _ _ _ = _
        rw [show m.succ = i.succ.castSucc by ext; change _ + 1 = _ + 1; rw [hm],
          Fin.insertNth_apply_same]
    · rw [Nat.lt_iff_add_one_le, le_iff_lt_or_eq] at hm
      obtain hm | hm := hm
      · convert! p.step ⟨m.1 - 1, Nat.sub_lt_right_of_lt_add (by lia) m.2⟩
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above (h := hm)]
          aesop
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap
          · exact hm.trans (lt_add_one _)
          simp only [Fin.pred_succ, eq_rec_constant, Fin.succ_mk]
          congr
exact Fin.ext Eq.symm Nat.succ_pred_eq_of_pos (lt_trans (Nat.zero_lt_succ _) hm)
      · convert! connect_next
        · change Fin.insertNth _ _ _ _ = _
          rw [show m.castSucc = i.succ.castSucc from Fin.ext hm.symm]; rw [Fin.insertNth_apply_same]
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap
          · change i.1 + 1 < m.1 + 1; lia
          simp only [Fin.pred_succ, eq_rec_constant]
          congr; ext; exact hm.symm

/--
A relation series `a₀ -r→ a₁ -r→ ... -r→ aₙ` of `r` gives a relation series of the reverse of `r`
by reversing the series `aₙ ←r- aₙ₋₁ ←r- ... ←r- a₁ ←r- a₀`.
-/
@[simps length]
/--
Definition of `reverse` / `reverse` 的定义

English:
definition reverse
  signature: (p : RelSeries r)
  body: p.length
  toFun := p ∘ Fin.rev
  step i := by
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [SetRel.mem_inv]
    have hi : i.1 + 1 <= p.length := by lia
    convert! p.step ⟨p.length - (i.1 + 1), Nat.sub_lt_self (by lia) hi⟩
    · ext; simp
    · ext
      simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
      lia

中文:
定义 reverse
  签名: (p : RelSeries r)
  定义体: p.length
  toFun := p ∘ Fin.rev
  step i := by
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [SetRel.mem_inv]
    have hi : i.1 + 1 <= p.length := by lia
    convert! p.step ⟨p.length - (i.1 + 1), Nat.sub_lt_self (by lia) hi⟩
    · ext; simp
    · ext
      simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
      lia

Depends on / 依赖: length, p.length
-/
def reverse (p : RelSeries r) : RelSeries r.inv where
  length := p.length
  toFun := p ∘ Fin.rev
  step i := by
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [SetRel.mem_inv]
    have hi : i.1 + 1 <= p.length := by lia
    convert! p.step ⟨p.length - (i.1 + 1), Nat.sub_lt_self (by lia) hi⟩
    · ext; simp
    · ext
      simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
      lia

/--
lemma `reverse_apply` / 引理 `reverse_apply`

English:
lemma reverse_apply
  given: (p : RelSeries r) (i : Fin (p.length + 1))
  proof: rfl

中文:
引理 reverse_apply
  条件: (p : RelSeries r) (i : 有限集 (p.length + 1))
  证明: rfl
-/
@[simp] lemma reverse_apply (p : RelSeries r) (i : Fin (p.length + 1)) :
    p.reverse i = p i.rev := rfl

set_option backward.defeqAttrib.useBackward true in
/--
lemma `last_reverse` / 引理 `last_reverse`

English:
lemma last_reverse
  given: (p : RelSeries r)
  statement: p.reverse.last = p.head
  proof: by
  simp [RelSeries.last, RelSeries.head]

中文:
引理 last_reverse
  条件: (p : RelSeries r)
  结论: p.reverse.last = p.head
  证明: by
  simp [RelSeries.last, RelSeries.head]
-/
@[simp] lemma last_reverse (p : RelSeries r) : p.reverse.last = p.head := by
  simp [RelSeries.last, RelSeries.head]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `head_reverse` / 引理 `head_reverse`

English:
lemma head_reverse
  given: (p : RelSeries r)
  statement: p.reverse.head = p.last
  proof: by
  simp [RelSeries.last, RelSeries.head]

中文:
引理 head_reverse
  条件: (p : RelSeries r)
  结论: p.reverse.head = p.last
  证明: by
  simp [RelSeries.last, RelSeries.head]
-/
@[simp] lemma head_reverse (p : RelSeries r) : p.reverse.head = p.last := by
  simp [RelSeries.last, RelSeries.head]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `reverse_reverse` / 引理 `reverse_reverse`

English:
lemma reverse_reverse
  given: {r : SetRel α α} (p : RelSeries r)
  statement: p.reverse.reverse = p
  proof: by
  ext <;> simp

中文:
引理 reverse_reverse
  条件: {r : SetRel α α} (p : RelSeries r)
  结论: p.reverse.reverse = p
  证明: by
  ext <;> simp
-/
@[simp] lemma reverse_reverse {r : SetRel α α} (p : RelSeries r) : p.reverse.reverse = p := by
  ext <;> simp

/--
Given a series `a₀ -r→ a₁ -r→ ... -r→ aₙ` and an `a` such that `a₀ -r→ a` holds, there is
a series of length `n+1`: `a -r→ a₀ -r→ a₁ -r→ ... -r→ aₙ`.
-/
@[simps! length]
/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (p : RelSeries r) (newHead : α) (rel : newHead ~[r] p.head)
  body: (singleton r newHead).append p rel

中文:
定义 cons
  签名: (p : RelSeries r) (newHead : α) (rel : newHead ~[r] p.head)
  定义体: (singleton r newHead).append p rel

Depends on / 依赖: append, newHead, singleton
-/
def cons (p : RelSeries r) (newHead : α) (rel : newHead ~[r] p.head) : RelSeries r :=
  (singleton r newHead).append p rel

/--
lemma `head_cons` / 引理 `head_cons`

English:
lemma head_cons
  given: (p : RelSeries r) (newHead : α) (rel : newHead ~[r] p.head)
  proof: rfl

中文:
引理 head_cons
  条件: (p : RelSeries r) (newHead : α) (rel : newHead ~[r] p.head)
  证明: rfl
-/
@[simp] lemma head_cons (p : RelSeries r) (newHead : α) (rel : newHead ~[r] p.head) :
    (p.cons newHead rel).head = newHead := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `last_cons` / 引理 `last_cons`

English:
lemma last_cons
  given: (p : RelSeries r) (newHead : α) (rel : newHead ~[r] p.head)
  proof: by
  delta cons
  rw [last_append]

中文:
引理 last_cons
  条件: (p : RelSeries r) (newHead : α) (rel : newHead ~[r] p.head)
  证明: by
  delta cons
  rw [last_append]
-/
@[simp] lemma last_cons (p : RelSeries r) (newHead : α) (rel : newHead ~[r] p.head) :
    (p.cons newHead rel).last = p.last := by
  delta cons
  rw [last_append]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `cons_cast_succ` / 引理 `cons_cast_succ`

English:
lemma cons_cast_succ
  given: (s : RelSeries r) (a : α) (h : a ~[r] s.head) (i : Fin (s.length + 1))
  proof: by
  simp [cons, Fin.append, Fin.addCases, Fin.subNat]

@[simp]

中文:
引理 cons_cast_succ
  条件: (s : RelSeries r) (a : α) (h : a ~[r] s.head) (i : 有限集 (s.length + 1))
  证明: by
  simp [cons, Fin.append, Fin.addCases, Fin.subNat]

@[simp]

Depends on / 依赖: Fin.addCases, Fin.append, Fin.subNat, addCases, append, subNat
-/
lemma cons_cast_succ (s : RelSeries r) (a : α) (h : a ~[r] s.head) (i : Fin (s.length + 1)) :
    (s.cons a h) (.cast (by simp) (.succ i)) = s i := by
  simp [cons, Fin.append, Fin.addCases, Fin.subNat]

@[simp]
/--
lemma `append_singleton_left` / 引理 `append_singleton_left`

English:
lemma append_singleton_left
  given: (p : RelSeries r) (x : α) (hx : x ~[r] p.head)
  proof: rfl

中文:
引理 append_singleton_left
  条件: (p : RelSeries r) (x : α) (hx : x ~[r] p.head)
  证明: rfl
-/
lemma append_singleton_left (p : RelSeries r) (x : α) (hx : x ~[r] p.head) :
    (singleton r x).append p hx = p.cons x hx :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `toList_cons` / 引理 `toList_cons`

English:
lemma toList_cons
  given: (p : RelSeries r) (x : α) (hx : x ~[r] p.head)
  proof: by
  rw [cons]; rw [toList_append]
  simp

中文:
引理 toList_cons
  条件: (p : RelSeries r) (x : α) (hx : x ~[r] p.head)
  证明: by
  rw [cons]; rw [toList_append]
  simp

Depends on / 依赖: toList_append
-/
lemma toList_cons (p : RelSeries r) (x : α) (hx : x ~[r] p.head) :
    (p.cons x hx).toList = x :: p.toList := by
  rw [cons]; rw [toList_append]
  simp

/--
lemma `fromListIsChain_cons` / 引理 `fromListIsChain_cons`

English:
lemma fromListIsChain_cons
  statement: (l : List α) (l_ne_nil : l != [])
  proof: by
  apply toList_injective
  simp

中文:
引理 fromListIsChain_cons
  结论: (l : 列表 α) (l_ne_nil : l != [])
  证明: by
  apply toList_injective
  simp

Depends on / 依赖: toList_injective
-/
lemma fromListIsChain_cons (l : List α) (l_ne_nil : l != [])
    (hl : l.IsChain (· ~[r] ·)) (x : α) (hx : x ~[r] l.head l_ne_nil) :
    fromListIsChain (x :: l) (by simp) (hl.cons_of_ne_nil l_ne_nil hx) =
      (fromListIsChain l l_ne_nil hl).cons x (by simpa) := by
  apply toList_injective
  simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `append_cons` / 引理 `append_cons`

English:
lemma append_cons
  given: {p q : RelSeries r} {x : α} (hx : x ~[r] p.head) (hq : p.last ~[r] q.head)
  proof: by
  simp only [cons]
  rw [append_assoc]

中文:
引理 append_cons
  条件: {p q : RelSeries r} {x : α} (hx : x ~[r] p.head) (hq : p.last ~[r] q.head)
  证明: by
  simp only [cons]
  rw [append_assoc]

Depends on / 依赖: append_assoc
-/
lemma append_cons {p q : RelSeries r} {x : α} (hx : x ~[r] p.head) (hq : p.last ~[r] q.head) :
    (p.cons x hx).append q (by simpa) = (p.append q hq).cons x (by simpa) := by
  simp only [cons]
  rw [append_assoc]

/--
Given a series `a₀ -r→ a₁ -r→ ... -r→ aₙ` and an `a` such that `aₙ -r→ a` holds, there is
a series of length `n+1`: `a₀ -r→ a₁ -r→ ... -r→ aₙ -r→ a`.
-/
@[simps! length]
/--
Definition of `snoc` / `snoc` 的定义

English:
definition snoc
  signature: (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast)
  body: p.append (singleton r newLast) rel

中文:
定义 snoc
  签名: (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast)
  定义体: p.append (singleton r newLast) rel

Depends on / 依赖: append, newLast, p.append, singleton
-/
def snoc (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast) : RelSeries r :=
  p.append (singleton r newLast) rel

set_option backward.isDefEq.respectTransparency false in
/--
lemma `head_snoc` / 引理 `head_snoc`

English:
lemma head_snoc
  given: (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast)
  proof: by
  delta snoc; rw [head_append]

中文:
引理 head_snoc
  条件: (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast)
  证明: by
  delta snoc; rw [head_append]
-/
@[simp] lemma head_snoc (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast) :
    (p.snoc newLast rel).head = p.head := by
  delta snoc; rw [head_append]

/--
lemma `last_snoc` / 引理 `last_snoc`

English:
lemma last_snoc
  given: (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast)
  proof: last_append _ _ _

中文:
引理 last_snoc
  条件: (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast)
  证明: last_append _ _ _
-/
@[simp] lemma last_snoc (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast) :
    (p.snoc newLast rel).last = newLast := last_append _ _ _

/--
lemma `snoc_cast_castSucc` / 引理 `snoc_cast_castSucc`

English:
lemma snoc_cast_castSucc
  given: (s : RelSeries r) (a : α) (h : s.last ~[r] a) (i : Fin (s.length + 1))
  proof: append_apply_left s (singleton r a) h i

中文:
引理 snoc_cast_castSucc
  条件: (s : RelSeries r) (a : α) (h : s.last ~[r] a) (i : 有限集 (s.length + 1))
  证明: append_apply_left s (singleton r a) h i

Depends on / 依赖: append_apply_left, singleton
-/
lemma snoc_cast_castSucc (s : RelSeries r) (a : α) (h : s.last ~[r] a) (i : Fin (s.length + 1)) :
    (s.snoc a h) (.cast (by simp) (.castSucc i)) = s i :=
  append_apply_left s (singleton r a) h i

-- This lemma is useful because `last_snoc` is about `Fin.last (p.snoc _ _).length`, but we often
-- see `Fin.last (p.length + 1)` in practice. They are equal by definition, but sometimes simplifier
-- does not pick up `last_snoc`
/--
lemma `last_snoc'` / 引理 `last_snoc'`

English:
lemma last_snoc'
  given: (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast)
  proof: last_append _ _ _

中文:
引理 last_snoc'
  条件: (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast)
  证明: last_append _ _ _
-/
@[simp] lemma last_snoc' (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast) :
    p.snoc newLast rel (Fin.last (p.length + 1)) = newLast := last_append _ _ _

/--
lemma `snoc_castSucc` / 引理 `snoc_castSucc`

English:
lemma snoc_castSucc
  statement: (s : RelSeries r) (a : α) (connect : s.last ~[r] a)
  proof: Fin.append_left _ _ i

中文:
引理 snoc_castSucc
  结论: (s : RelSeries r) (a : α) (connect : s.last ~[r] a)
  证明: Fin.append_left _ _ i
-/
@[simp] lemma snoc_castSucc (s : RelSeries r) (a : α) (connect : s.last ~[r] a)
    (i : Fin (s.length + 1)) : snoc s a connect (Fin.castSucc i) = s i :=
  Fin.append_left _ _ i

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_snoc` / 引理 `mem_snoc`

English:
lemma mem_snoc
  given: {p : RelSeries r} {newLast : α} {rel : p.last ~[r] newLast} {x : α}
  proof: by
  simp only [snoc, append, mem_def, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact Fin.lastCases (Or.inr <| Fin.append_right _ _ 0) (fun i => Or.inl ⟨⟨i.1, i.2⟩,
      (Fin.append_left _ _ _).symm⟩) i
  · intro h
    rcases h with (⟨i, rfl⟩ | rfl)
    · exact ⟨i.castSucc, Fin.append_left _ _ _⟩
    · exact ⟨Fin.last _, Fin.append_right _ _ 0⟩

中文:
引理 mem_snoc
  条件: {p : RelSeries r} {newLast : α} {rel : p.last ~[r] newLast} {x : α}
  证明: by
  simp only [snoc, append, mem_def, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact Fin.lastCases (Or.inr <| Fin.append_right _ _ 0) (fun i => Or.inl ⟨⟨i.1, i.2⟩,
      (Fin.append_left _ _ _).symm⟩) i
  · intro h
    rcases h with (⟨i, rfl⟩ | rfl)
    · exact ⟨i.castSucc, Fin.append_left _ _ _⟩
    · exact ⟨Fin.last _, Fin.append_right _ _ 0⟩

Depends on / 依赖: Fin.append_left, Fin.append_right, Fin.last, Fin.lastCases, Or.inl, Or.inr, Set.mem_range, append, append_left, append_right, castSucc, i.castSucc, lastCases, mem_def, mem_range
-/
lemma mem_snoc {p : RelSeries r} {newLast : α} {rel : p.last ~[r] newLast} {x : α} :
    x in p.snoc newLast rel ↔ x in p ∨ x = newLast := by
  simp only [snoc, append, mem_def, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact Fin.lastCases (Or.inr <| Fin.append_right _ _ 0) (fun i => Or.inl ⟨⟨i.1, i.2⟩,
      (Fin.append_left _ _ _).symm⟩) i
  · intro h
    rcases h with (⟨i, rfl⟩ | rfl)
    · exact ⟨i.castSucc, Fin.append_left _ _ _⟩
    · exact ⟨Fin.last _, Fin.append_right _ _ 0⟩

/--
If a series `a₀ -r→ a₁ -r→ ...` has positive length, then `a₁ -r→ ...` is another series
-/
@[simps]
/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: (p : RelSeries r) (len_pos : p.length != 0)
  body: p.length - 1
  toFun := Fin.tail p ∘ (Fin.cast <| Nat.succ_pred_eq_of_pos <| Nat.pos_of_ne_zero len_pos)
  step i := p.step ⟨i.1 + 1, Nat.lt_pred_iff.mp i.2⟩

中文:
定义 tail
  签名: (p : RelSeries r) (len_pos : p.length != 0)
  定义体: p.length - 1
  toFun := Fin.tail p ∘ (Fin.cast <| Nat.succ_pred_eq_of_pos <| Nat.pos_of_ne_zero len_pos)
  step i := p.step ⟨i.1 + 1, Nat.lt_pred_iff.mp i.2⟩

Depends on / 依赖: length, p.length
-/
def tail (p : RelSeries r) (len_pos : p.length != 0) : RelSeries r where
  length := p.length - 1
  toFun := Fin.tail p ∘ (Fin.cast <| Nat.succ_pred_eq_of_pos <| Nat.pos_of_ne_zero len_pos)
  step i := p.step ⟨i.1 + 1, Nat.lt_pred_iff.mp i.2⟩

/--
lemma `head_tail` / 引理 `head_tail`

English:
lemma head_tail
  given: (p : RelSeries r) (len_pos : p.length != 0)
  proof: by
  change p (Fin.succ _) = p 1
  congr
  ext
  change (1 : Nat) = (1 : Nat) % _
  rw [Nat.mod_eq_of_lt]
  simpa only [lt_add_iff_pos_left, Nat.pos_iff_ne_zero]

中文:
引理 head_tail
  条件: (p : RelSeries r) (len_pos : p.length != 0)
  证明: by
  change p (Fin.succ _) = p 1
  congr
  ext
  change (1 : Nat) = (1 : Nat) % _
  rw [Nat.mod_eq_of_lt]
  simpa only [lt_add_iff_pos_left, Nat.pos_iff_ne_zero]

Depends on / 依赖: IsLiesOverAlgebra, algebraOfLiesOver
-/
@[simp] lemma head_tail (p : RelSeries r) (len_pos : p.length != 0) :
    (p.tail len_pos).head = p 1 := by
  change p (Fin.succ _) = p 1
  congr
  ext
  change (1 : Nat) = (1 : Nat) % _
  rw [Nat.mod_eq_of_lt]
  simpa only [lt_add_iff_pos_left, Nat.pos_iff_ne_zero]

/--
lemma `last_tail` / 引理 `last_tail`

English:
lemma last_tail
  given: (p : RelSeries r) (len_pos : p.length != 0)
  proof: by
  change p _ = p _
  congr
  ext
  simp only [Fin.val_succ, Fin.val_last]
  exact Nat.succ_pred_eq_of_pos (by simpa [Nat.pos_iff_ne_zero] using len_pos)

中文:
引理 last_tail
  条件: (p : RelSeries r) (len_pos : p.length != 0)
  证明: by
  change p _ = p _
  congr
  ext
  simp only [Fin.val_succ, Fin.val_last]
  exact Nat.succ_pred_eq_of_pos (by simpa [Nat.pos_iff_ne_zero] using len_pos)

Depends on / 依赖: AtPrime, IsLiesOverAlgebra, IsLiesOverAlgebra.algebraMap_eq, IsScalarTower, IsScalarTower.algebraMap_apply, Localization, Localization.AtPrime, Localization.localRingHom_to_map, algebraMap_apply, algebraMap_eq, localRingHom_to_map, of_algebraMap_eq
-/
@[simp] lemma last_tail (p : RelSeries r) (len_pos : p.length != 0) :
    (p.tail len_pos).last = p.last := by
  change p _ = p _
  congr
  ext
  simp only [Fin.val_succ, Fin.val_last]
  exact Nat.succ_pred_eq_of_pos (by simpa [Nat.pos_iff_ne_zero] using len_pos)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `toList_tail` / 引理 `toList_tail`

English:
lemma toList_tail
  given: {p : RelSeries r} (hp : p.length != 0)
  statement: (p.tail hp).toList = p.toList.tail
  proof: by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp
    lia
  · simp [Fin.tail]

@[simp]

中文:
引理 toList_tail
  条件: {p : RelSeries r} (hp : p.length != 0)
  结论: (p.tail hp).toList = p.toList.tail
  证明: by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp
    lia
  · simp [Fin.tail]

@[simp]

Depends on / 依赖: Fin.tail, IsLiesOverAlgebra, IsLiesOverAlgebra.algebraMap_eq, IsScalarTower, IsScalarTower.algebraMap_eq, List.ext_getElem, algebraMap_eq, ext_getElem, localRingHom_comp, of_algebraMap_eq
-/
lemma toList_tail {p : RelSeries r} (hp : p.length != 0) : (p.tail hp).toList = p.toList.tail := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp
    lia
  · simp [Fin.tail]

@[simp]
/--
lemma `tail_cons` / 引理 `tail_cons`

English:
lemma tail_cons
  given: (p : RelSeries r) (x : α) (hx : x ~[r] p.head)
  proof: by
  apply toList_injective
  simp

中文:
引理 tail_cons
  条件: (p : RelSeries r) (x : α) (hx : x ~[r] p.head)
  证明: by
  apply toList_injective
  simp

Depends on / 依赖: toList_injective
-/
lemma tail_cons (p : RelSeries r) (x : α) (hx : x ~[r] p.head) :
    (p.cons x hx).tail (by simp) = p := by
  apply toList_injective
  simp

/--
lemma `cons_self_tail` / 引理 `cons_self_tail`

English:
lemma cons_self_tail
  given: {p : RelSeries r} (hp : p.length != 0)
  proof: by
  apply toList_injective
  simp [← head_toList]

中文:
引理 cons_self_tail
  条件: {p : RelSeries r} (hp : p.length != 0)
  证明: by
  apply toList_injective
  simp [← head_toList]

Depends on / 依赖: head_toList, toList_injective
-/
lemma cons_self_tail {p : RelSeries r} (hp : p.length != 0) :
    (p.tail hp).cons p.head (p.3 ⟨0, Nat.zero_lt_of_ne_zero hp⟩) = p := by
  apply toList_injective
  simp [← head_toList]

set_option backward.isDefEq.respectTransparency false in
/--
To show a proposition `p` for `xs : RelSeries r` it suffices to show it for all singletons
and to show that when `p` holds for `xs` it also holds for `xs` prepended with one element.

Note: This can also be used to construct data, but it does not have good definitional properties,
since `(p.cons x hx).tail _ = p` is not a definitional equality.
-/
@[elab_as_elim]
/--
Definition of `inductionOn` / `inductionOn` 的定义

English:
definition inductionOn
  signature: (motive : RelSeries r -> Sort*)
  body: by
  let {n : Nat} (heq : p.length = n) : motive p := by
    induction n generalizing p with
    | zero =>
      convert! singleton p.head
      ext n
      · exact heq
      simp [show n = 0 by lia, apply_zero]
    | succ d hd =>
      have lq := p.tail_length (heq ▸ d.zero_ne_add_one.symm)
      nth_rw 3 [heq] at lq
      convert!
        cons (p.tail (heq ▸ d.zero_ne_add_one.symm)) p.head (p.3 ⟨0, heq ▸ d.zero_lt_succ⟩)
          (hd _ lq)
      exact (p.cons_self_tail (heq ▸ d.zero_ne_add_one.symm)).symm
  exact this rfl

中文:
定义 inductionOn
  签名: (motive : RelSeries r -> 类型层*)
  定义体: by
  let {n : Nat} (heq : p.length = n) : motive p := by
    induction n generalizing p with
    | zero =>
      convert! singleton p.head
      ext n
      · exact heq
      simp [show n = 0 by lia, apply_zero]
    | succ d hd =>
      have lq := p.tail_length (heq ▸ d.zero_ne_add_one.symm)
      nth_rw 3 [heq] at lq
      convert!
        cons (p.tail (heq ▸ d.zero_ne_add_one.symm)) p.head (p.3 ⟨0, heq ▸ d.zero_lt_succ⟩)
          (hd _ lq)
      exact (p.cons_self_tail (heq ▸ d.zero_ne_add_one.symm)).symm
  exact this rfl

Depends on / 依赖: apply_zero, cons_self_tail, convert, d.zero_lt_succ, d.zero_ne_add_one.symm, generalizing, length, motive, nth_rw, p.cons_self_tail, p.head, p.length, p.tail, p.tail_length, singleton, tail_length, zero_lt_succ, zero_ne_add_one
-/
def inductionOn (motive : RelSeries r -> Sort*)
    (singleton : (x : α) -> motive (RelSeries.singleton r x))
    (cons : (p : RelSeries r) -> (x : α) -> (hx : x ~[r] p.head) -> (hp : motive p) ->
      motive (p.cons x hx)) (p : RelSeries r) :
    motive p := by
  let {n : Nat} (heq : p.length = n) : motive p := by
    induction n generalizing p with
    | zero =>
      convert! singleton p.head
      ext n
      · exact heq
      simp [show n = 0 by lia, apply_zero]
    | succ d hd =>
      have lq := p.tail_length (heq ▸ d.zero_ne_add_one.symm)
      nth_rw 3 [heq] at lq
      convert!
        cons (p.tail (heq ▸ d.zero_ne_add_one.symm)) p.head (p.3 ⟨0, heq ▸ d.zero_lt_succ⟩)
          (hd _ lq)
      exact (p.cons_self_tail (heq ▸ d.zero_ne_add_one.symm)).symm
  exact this rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `toList_snoc` / 引理 `toList_snoc`

English:
lemma toList_snoc
  given: (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast)
  proof: by
  simp [snoc]

中文:
引理 toList_snoc
  条件: (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast)
  证明: by
  simp [snoc]
-/
lemma toList_snoc (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast) :
    (p.snoc newLast rel).toList = p.toList ++ [newLast] := by
  simp [snoc]

/--
If a series ``a₀ -r→ a₁ -r→ ... -r→ aₙ``, then `a₀ -r→ a₁ -r→ ... -r→ aₙ₋₁` is
another series -/
@[simps]
/--
Definition of `eraseLast` / `eraseLast` 的定义

English:
definition eraseLast
  signature: (p : RelSeries r)
  body: p.length - 1
  toFun i := p ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ (Nat.sub_le _ _))⟩
  step i := p.step ⟨i, lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩

中文:
定义 eraseLast
  签名: (p : RelSeries r)
  定义体: p.length - 1
  toFun i := p ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ (Nat.sub_le _ _))⟩
  step i := p.step ⟨i, lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩

Depends on / 依赖: length, p.length
-/
def eraseLast (p : RelSeries r) : RelSeries r where
  length := p.length - 1
  toFun i := p ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ (Nat.sub_le _ _))⟩
  step i := p.step ⟨i, lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩

/--
lemma `head_eraseLast` / 引理 `head_eraseLast`

English:
lemma head_eraseLast
  given: (p : RelSeries r)
  statement: p.eraseLast.head = p.head
  proof: rfl

中文:
引理 head_eraseLast
  条件: (p : RelSeries r)
  结论: p.eraseLast.head = p.head
  证明: rfl
-/
@[simp] lemma head_eraseLast (p : RelSeries r) : p.eraseLast.head = p.head := rfl

/--
lemma `last_eraseLast` / 引理 `last_eraseLast`

English:
lemma last_eraseLast
  given: (p : RelSeries r)
  proof: rfl

中文:
引理 last_eraseLast
  条件: (p : RelSeries r)
  证明: rfl
-/
@[simp] lemma last_eraseLast (p : RelSeries r) :
    p.eraseLast.last = p ⟨p.length.pred, Nat.lt_succ_iff.2 (Nat.pred_le _)⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `eraseLast_last_rel_last` / 引理 `eraseLast_last_rel_last`

English:
lemma eraseLast_last_rel_last
  given: (p : RelSeries r) (h : p.length != 0)
  proof: by
  simp only [last, Fin.last, eraseLast_length, eraseLast_toFun]
  convert! p.step ⟨p.length - 1, by lia⟩
  simp only [Fin.succ_mk]; lia

中文:
引理 eraseLast_last_rel_last
  条件: (p : RelSeries r) (h : p.length != 0)
  证明: by
  simp only [last, Fin.last, eraseLast_length, eraseLast_toFun]
  convert! p.step ⟨p.length - 1, by lia⟩
  simp only [Fin.succ_mk]; lia

Depends on / 依赖: Fin.last, Fin.succ_mk, convert, eraseLast_length, eraseLast_toFun, length, p.length, p.step, succ_mk
-/
lemma eraseLast_last_rel_last (p : RelSeries r) (h : p.length != 0) :
    p.eraseLast.last ~[r] p.last := by
  simp only [last, Fin.last, eraseLast_length, eraseLast_toFun]
  convert! p.step ⟨p.length - 1, by lia⟩
  simp only [Fin.succ_mk]; lia

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `toList_eraseLast` / 引理 `toList_eraseLast`

English:
lemma toList_eraseLast
  given: (p : RelSeries r) (hp : p.length != 0)
  proof: by
  apply List.ext_getElem
  · simpa using Nat.succ_pred_eq_of_ne_zero hp
  · intro i hi h2
    simp

中文:
引理 toList_eraseLast
  条件: (p : RelSeries r) (hp : p.length != 0)
  证明: by
  apply List.ext_getElem
  · simpa using Nat.succ_pred_eq_of_ne_zero hp
  · intro i hi h2
    simp

Depends on / 依赖: List.ext_getElem, Nat.succ_pred_eq_of_ne_zero, ext_getElem, succ_pred_eq_of_ne_zero
-/
lemma toList_eraseLast (p : RelSeries r) (hp : p.length != 0) :
    p.eraseLast.toList = p.toList.dropLast := by
  apply List.ext_getElem
  · simpa using Nat.succ_pred_eq_of_ne_zero hp
  · intro i hi h2
    simp

/--
lemma `snoc_self_eraseLast` / 引理 `snoc_self_eraseLast`

English:
lemma snoc_self_eraseLast
  given: (p : RelSeries r) (h : p.length != 0)
  proof: by
  apply toList_injective
  rw [toList_snoc]; rw [← getLast_toList]; rw [toList_eraseLast _ h]; rw [List.dropLast_append_getLast]

中文:
引理 snoc_self_eraseLast
  条件: (p : RelSeries r) (h : p.length != 0)
  证明: by
  apply toList_injective
  rw [toList_snoc]; rw [← getLast_toList]; rw [toList_eraseLast _ h]; rw [List.dropLast_append_getLast]

Depends on / 依赖: List.dropLast_append_getLast, dropLast_append_getLast, getLast_toList, toList_eraseLast, toList_injective, toList_snoc
-/
lemma snoc_self_eraseLast (p : RelSeries r) (h : p.length != 0) :
    p.eraseLast.snoc p.last (p.eraseLast_last_rel_last h) = p := by
  apply toList_injective
  rw [toList_snoc]; rw [← getLast_toList]; rw [toList_eraseLast _ h]; rw [List.dropLast_append_getLast]

set_option backward.isDefEq.respectTransparency false in
/--
To show a proposition `p` for `xs : RelSeries r` it suffices to show it for all singletons
and to show that when `p` holds for `xs` it also holds for `xs` appended with one element.
-/
@[elab_as_elim]
/--
Definition of `inductionOn'` / `inductionOn'` 的定义

English:
definition inductionOn'
  signature: (motive : RelSeries r -> Sort*)
  body: by
  let {n : Nat} (heq : p.length = n) : motive p := by
    induction n generalizing p with
    | zero =>
      convert! singleton p.head
      ext n
      · exact heq
      · simp [show n = 0 by lia, apply_zero]
    | succ d hd =>
      have ne0 : p.length != 0 := by simp [heq]
      have len : p.eraseLast.length = d := by simp [heq]
      convert! snoc p.eraseLast p.last (p.eraseLast_last_rel_last ne0) (hd _ len)
      exact (p.snoc_self_eraseLast ne0).symm
  exact this rfl

中文:
定义 inductionOn'
  签名: (motive : RelSeries r -> 类型层*)
  定义体: by
  let {n : Nat} (heq : p.length = n) : motive p := by
    induction n generalizing p with
    | zero =>
      convert! singleton p.head
      ext n
      · exact heq
      · simp [show n = 0 by lia, apply_zero]
    | succ d hd =>
      have ne0 : p.length != 0 := by simp [heq]
      have len : p.eraseLast.length = d := by simp [heq]
      convert! snoc p.eraseLast p.last (p.eraseLast_last_rel_last ne0) (hd _ len)
      exact (p.snoc_self_eraseLast ne0).symm
  exact this rfl

Depends on / 依赖: apply_zero, convert, eraseLast, eraseLast_last_rel_last, generalizing, length, motive, p.eraseLast, p.eraseLast.length, p.eraseLast_last_rel_last, p.head, p.last, p.length, p.snoc_self_eraseLast, singleton, snoc_self_eraseLast
-/
def inductionOn' (motive : RelSeries r -> Sort*)
    (singleton : (x : α) -> motive (RelSeries.singleton r x))
    (snoc : (p : RelSeries r) -> (x : α) -> (hx : p.last ~[r] x) -> (hp : motive p) ->
      motive (p.snoc x hx)) (p : RelSeries r) :
    motive p := by
  let {n : Nat} (heq : p.length = n) : motive p := by
    induction n generalizing p with
    | zero =>
      convert! singleton p.head
      ext n
      · exact heq
      · simp [show n = 0 by lia, apply_zero]
    | succ d hd =>
      have ne0 : p.length != 0 := by simp [heq]
      have len : p.eraseLast.length = d := by simp [heq]
      convert! snoc p.eraseLast p.last (p.eraseLast_last_rel_last ne0) (hd _ len)
      exact (p.snoc_self_eraseLast ne0).symm
  exact this rfl

/--
Given two series of the form `a₀ -r→ ... -r→ X` and `X -r→ b ---> ...`,
then `a₀ -r→ ... -r→ X -r→ b ...` is another series obtained by combining the given two.
-/
@[simps length]
/--
Definition of `smash` / `smash` 的定义

English:
definition smash
  signature: (p q : RelSeries r) (connect : p.last = q.head)
  body: p.length + q.length
  toFun := Fin.addCases (m := p.length) (n := q.length + 1) (p ∘ Fin.castSucc) q
  step := by
    apply Fin.addCases <;> intro i
    · simp_rw [Fin.castSucc_castAdd, Fin.addCases_left, Fin.succ_castAdd]
      convert! p.step i
      split_ifs with h
      · rw [Fin.addCases_right, h, ← last, connect, head]
      · apply Fin.addCases_left
    simpa only [Fin.castSucc_natAdd, Fin.succ_natAdd, Fin.addCases_right] using q.step i

中文:
定义 smash
  签名: (p q : RelSeries r) (connect : p.last = q.head)
  定义体: p.length + q.length
  toFun := Fin.addCases (m := p.length) (n := q.length + 1) (p ∘ Fin.castSucc) q
  step := by
    apply Fin.addCases <;> intro i
    · simp_rw [Fin.castSucc_castAdd, Fin.addCases_left, Fin.succ_castAdd]
      convert! p.step i
      split_ifs with h
      · rw [Fin.addCases_right, h, ← last, connect, head]
      · apply Fin.addCases_left
    simpa only [Fin.castSucc_natAdd, Fin.succ_natAdd, Fin.addCases_right] using q.step i

Depends on / 依赖: length, p.length, q.length
-/
def smash (p q : RelSeries r) (connect : p.last = q.head) : RelSeries r where
  length := p.length + q.length
  toFun := Fin.addCases (m := p.length) (n := q.length + 1) (p ∘ Fin.castSucc) q
  step := by
    apply Fin.addCases <;> intro i
    · simp_rw [Fin.castSucc_castAdd, Fin.addCases_left, Fin.succ_castAdd]
      convert! p.step i
      split_ifs with h
      · rw [Fin.addCases_right, h, ← last, connect, head]
      · apply Fin.addCases_left
    simpa only [Fin.castSucc_natAdd, Fin.succ_natAdd, Fin.addCases_right] using q.step i

/--
lemma `smash_castLE` / 引理 `smash_castLE`

English:
lemma smash_castLE
  given: {p q : RelSeries r} (h : p.last = q.head) (i : Fin (p.length + 1))
  proof: by
  refine i.lastCases ?_ fun _ => by dsimp only [smash]; apply Fin.addCases_left
  change p.smash q h (Fin.natAdd p.length (0 : Fin (q.length + 1))) = _
  simpa only [smash, Fin.addCases_right] using! h.symm

中文:
引理 smash_castLE
  条件: {p q : RelSeries r} (h : p.last = q.head) (i : 有限集 (p.length + 1))
  证明: by
  refine i.lastCases ?_ fun _ => by dsimp only [smash]; apply Fin.addCases_left
  change p.smash q h (Fin.natAdd p.length (0 : Fin (q.length + 1))) = _
  simpa only [smash, Fin.addCases_right] using! h.symm

Depends on / 依赖: Fin.addCases_left, Fin.addCases_right, Fin.natAdd, addCases_left, addCases_right, h.symm, i.lastCases, lastCases, length, natAdd, p.length, p.smash, q.length
-/
lemma smash_castLE {p q : RelSeries r} (h : p.last = q.head) (i : Fin (p.length + 1)) :
    p.smash q h (i.castLE (by simp)) = p i := by
  refine i.lastCases ?_ fun _ => by dsimp only [smash]; apply Fin.addCases_left
  change p.smash q h (Fin.natAdd p.length (0 : Fin (q.length + 1))) = _
  simpa only [smash, Fin.addCases_right] using! h.symm

/--
lemma `smash_castAdd` / 引理 `smash_castAdd`

English:
lemma smash_castAdd
  given: {p q : RelSeries r} (h : p.last = q.head) (i : Fin p.length)
  proof: smash_castLE h i.castSucc

中文:
引理 smash_castAdd
  条件: {p q : RelSeries r} (h : p.last = q.head) (i : 有限集 p.length)
  证明: smash_castLE h i.castSucc

Depends on / 依赖: castSucc, i.castSucc, smash_castLE
-/
lemma smash_castAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin p.length) :
    p.smash q h (i.castAdd q.length).castSucc = p i.castSucc :=
  smash_castLE h i.castSucc

/--
lemma `smash_succ_castAdd` / 引理 `smash_succ_castAdd`

English:
lemma smash_succ_castAdd
  statement: {p q : RelSeries r} (h : p.last = q.head)
  proof: smash_castLE h i.succ

中文:
引理 smash_succ_castAdd
  结论: {p q : RelSeries r} (h : p.last = q.head)
  证明: smash_castLE h i.succ

Depends on / 依赖: i.succ, smash_castLE
-/
lemma smash_succ_castAdd {p q : RelSeries r} (h : p.last = q.head)
    (i : Fin p.length) : p.smash q h (i.castAdd q.length).succ = p i.succ :=
  smash_castLE h i.succ

/--
lemma `smash_natAdd` / 引理 `smash_natAdd`

English:
lemma smash_natAdd
  given: {p q : RelSeries r} (h : p.last = q.head) (i : Fin q.length)
  proof: by
  dsimp only [smash, Fin.castSucc_natAdd]
  apply Fin.addCases_right

中文:
引理 smash_natAdd
  条件: {p q : RelSeries r} (h : p.last = q.head) (i : 有限集 q.length)
  证明: by
  dsimp only [smash, Fin.castSucc_natAdd]
  apply Fin.addCases_right

Depends on / 依赖: Fin.addCases_right, Fin.castSucc_natAdd, addCases_right, castSucc_natAdd
-/
lemma smash_natAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin q.length) :
    smash p q h (i.natAdd p.length).castSucc = q i.castSucc := by
  dsimp only [smash, Fin.castSucc_natAdd]
  apply Fin.addCases_right

/--
lemma `smash_succ_natAdd` / 引理 `smash_succ_natAdd`

English:
lemma smash_succ_natAdd
  given: {p q : RelSeries r} (h : p.last = q.head) (i : Fin q.length)
  proof: by
  dsimp only [smash, Fin.succ_natAdd]
  apply Fin.addCases_right

中文:
引理 smash_succ_natAdd
  条件: {p q : RelSeries r} (h : p.last = q.head) (i : 有限集 q.length)
  证明: by
  dsimp only [smash, Fin.succ_natAdd]
  apply Fin.addCases_right

Depends on / 依赖: Fin.addCases_right, Fin.succ_natAdd, addCases_right, succ_natAdd
-/
lemma smash_succ_natAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin q.length) :
    smash p q h (i.natAdd p.length).succ = q i.succ := by
  dsimp only [smash, Fin.succ_natAdd]
  apply Fin.addCases_right

/--
lemma `head_smash` / 引理 `head_smash`

English:
lemma head_smash
  given: {p q : RelSeries r} (h : p.last = q.head)
  proof: by
  obtain ⟨_ | _, _⟩ := p
  · simpa [Fin.addCases] using! h.symm
  dsimp only [smash, head]
  exact Fin.addCases_left 0

中文:
引理 head_smash
  条件: {p q : RelSeries r} (h : p.last = q.head)
  证明: by
  obtain ⟨_ | _, _⟩ := p
  · simpa [Fin.addCases] using! h.symm
  dsimp only [smash, head]
  exact Fin.addCases_left 0
-/
@[simp] lemma head_smash {p q : RelSeries r} (h : p.last = q.head) :
    (smash p q h).head = p.head := by
  obtain ⟨_ | _, _⟩ := p
  · simpa [Fin.addCases] using! h.symm
  dsimp only [smash, head]
  exact Fin.addCases_left 0

/--
lemma `last_smash` / 引理 `last_smash`

English:
lemma last_smash
  given: {p q : RelSeries r} (h : p.last = q.head)
  proof: by
  dsimp only [smash, last]
  rw [← Fin.natAdd_last]; rw [Fin.addCases_right]

中文:
引理 last_smash
  条件: {p q : RelSeries r} (h : p.last = q.head)
  证明: by
  dsimp only [smash, last]
  rw [← Fin.natAdd_last]; rw [Fin.addCases_right]
-/
@[simp] lemma last_smash {p q : RelSeries r} (h : p.last = q.head) :
    (smash p q h).last = q.last := by
  dsimp only [smash, last]
  rw [← Fin.natAdd_last]; rw [Fin.addCases_right]

/-- Given the series `a₀ -r→ … -r→ aᵢ -r→ … -r→ aₙ`, the series `a₀ -r→ … -r→ aᵢ`. -/
@[simps! length]
/--
Definition of `take` / `take` 的定义

English:
definition take
  signature: {r : SetRel α α} (p : RelSeries r) (i : Fin (p.length + 1))
  body: i
  toFun := fun ⟨j, h⟩ => p.toFun ⟨j, by lia⟩
  step := fun ⟨j, h⟩ => p.step ⟨j, by lia⟩

@[simp]

中文:
定义 take
  签名: {r : SetRel α α} (p : RelSeries r) (i : 有限集 (p.length + 1))
  定义体: i
  toFun := fun ⟨j, h⟩ => p.toFun ⟨j, by lia⟩
  step := fun ⟨j, h⟩ => p.step ⟨j, by lia⟩

@[simp]
-/
def take {r : SetRel α α} (p : RelSeries r) (i : Fin (p.length + 1)) : RelSeries r where
  length := i
  toFun := fun ⟨j, h⟩ => p.toFun ⟨j, by lia⟩
  step := fun ⟨j, h⟩ => p.step ⟨j, by lia⟩

@[simp]
/--
lemma `head_take` / 引理 `head_take`

English:
lemma head_take
  given: (p : RelSeries r) (i : Fin (p.length + 1))
  proof: by simp [take, head]

@[simp]

中文:
引理 head_take
  条件: (p : RelSeries r) (i : 有限集 (p.length + 1))
  证明: by simp [take, head]

@[simp]
-/
lemma head_take (p : RelSeries r) (i : Fin (p.length + 1)) :
    (p.take i).head = p.head := by simp [take, head]

@[simp]
/--
lemma `last_take` / 引理 `last_take`

English:
lemma last_take
  given: (p : RelSeries r) (i : Fin (p.length + 1))
  proof: by simp [take, last, Fin.last]

中文:
引理 last_take
  条件: (p : RelSeries r) (i : 有限集 (p.length + 1))
  证明: by simp [take, last, Fin.last]

Depends on / 依赖: Fin.last
-/
lemma last_take (p : RelSeries r) (i : Fin (p.length + 1)) :
    (p.take i).last = p i := by simp [take, last, Fin.last]

/-- Given the series `a₀ -r→ … -r→ aᵢ -r→ … -r→ aₙ`, the series `aᵢ₊₁ -r→ … -r→ aₙ`. -/
@[simps! length]
/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: (p : RelSeries r) (i : Fin (p.length + 1))
  body: p.length - i
  toFun := fun ⟨j, h⟩ => p.toFun ⟨j+i, by lia⟩
  step := fun ⟨j, h⟩ => by
    convert! p.step ⟨j + i.1, by lia⟩
    simp only [Fin.succ_mk]; lia

@[simp]

中文:
定义 drop
  签名: (p : RelSeries r) (i : 有限集 (p.length + 1))
  定义体: p.length - i
  toFun := fun ⟨j, h⟩ => p.toFun ⟨j+i, by lia⟩
  step := fun ⟨j, h⟩ => by
    convert! p.step ⟨j + i.1, by lia⟩
    simp only [Fin.succ_mk]; lia

@[simp]

Depends on / 依赖: length, p.length
-/
def drop (p : RelSeries r) (i : Fin (p.length + 1)) : RelSeries r where
  length := p.length - i
  toFun := fun ⟨j, h⟩ => p.toFun ⟨j+i, by lia⟩
  step := fun ⟨j, h⟩ => by
    convert! p.step ⟨j + i.1, by lia⟩
    simp only [Fin.succ_mk]; lia

@[simp]
/--
lemma `head_drop` / 引理 `head_drop`

English:
lemma head_drop
  given: (p : RelSeries r) (i : Fin (p.length + 1))
  statement: (p.drop i).head = p.toFun i
  proof: by
  simp [drop, head]

@[simp]

中文:
引理 head_drop
  条件: (p : RelSeries r) (i : 有限集 (p.length + 1))
  结论: (p.drop i).head = p.toFun i
  证明: by
  simp [drop, head]

@[simp]
-/
lemma head_drop (p : RelSeries r) (i : Fin (p.length + 1)) : (p.drop i).head = p.toFun i := by
  simp [drop, head]

@[simp]
/--
lemma `last_drop` / 引理 `last_drop`

English:
lemma last_drop
  given: (p : RelSeries r) (i : Fin (p.length + 1))
  statement: (p.drop i).last = p.last
  proof: by
  simp only [last, drop, Fin.last]
  congr
  lia

中文:
引理 last_drop
  条件: (p : RelSeries r) (i : 有限集 (p.length + 1))
  结论: (p.drop i).last = p.last
  证明: by
  simp only [last, drop, Fin.last]
  congr
  lia

Depends on / 依赖: Fin.last
-/
lemma last_drop (p : RelSeries r) (i : Fin (p.length + 1)) : (p.drop i).last = p.last := by
  simp only [last, drop, Fin.last]
  congr
  lia

end RelSeries

variable {r} in
/--
lemma `SetRel.not_finiteDimensional_iff` / 引理 `SetRel.not_finiteDimensional_iff`

English:
lemma SetRel.not_finiteDimensional_iff
  given: [Nonempty α]
  proof: by
  rw [finiteDimensional_iff]; rw [infiniteDimensional_iff]
  push Not
  constructor
  · intro H n
    induction n with
    | zero => refine ⟨⟨0, ![_root_.Nonempty.some ‹_›], by simp⟩, by simp⟩
    | succ n IH =>
      obtain ⟨l, hl⟩ := IH
      obtain ⟨l', hl'⟩ := H l
      exact ⟨l'.take ⟨n + 1, by simpa [hl] using hl'⟩, rfl⟩
  · intro H l
    obtain ⟨l', hl'⟩ := H (l.length + 1)
    exact ⟨l', by simp [hl']⟩

中文:
引理 SetRel.not_finiteDimensional_iff
  条件: [非空 α]
  证明: by
  rw [finiteDimensional_iff]; rw [infiniteDimensional_iff]
  push Not
  constructor
  · intro H n
    induction n with
    | zero => refine ⟨⟨0, ![_root_.Nonempty.some ‹_›], by simp⟩, by simp⟩
    | succ n IH =>
      obtain ⟨l, hl⟩ := IH
      obtain ⟨l', hl'⟩ := H l
      exact ⟨l'.take ⟨n + 1, by simpa [hl] using hl'⟩, rfl⟩
  · intro H l
    obtain ⟨l', hl'⟩ := H (l.length + 1)
    exact ⟨l', by simp [hl']⟩

Depends on / 依赖: Nonempty, _root_, _root_.Nonempty.some, finiteDimensional_iff, infiniteDimensional_iff, l.length, length
-/
lemma SetRel.not_finiteDimensional_iff [Nonempty α] :
    ¬ r.FiniteDimensional ↔ r.InfiniteDimensional := by
  rw [finiteDimensional_iff]; rw [infiniteDimensional_iff]
  push Not
  constructor
  · intro H n
    induction n with
    | zero => refine ⟨⟨0, ![_root_.Nonempty.some ‹_›], by simp⟩, by simp⟩
    | succ n IH =>
      obtain ⟨l, hl⟩ := IH
      obtain ⟨l', hl'⟩ := H l
      exact ⟨l'.take ⟨n + 1, by simpa [hl] using hl'⟩, rfl⟩
  · intro H l
    obtain ⟨l', hl'⟩ := H (l.length + 1)
    exact ⟨l', by simp [hl']⟩

variable {r} in
/--
lemma `SetRel.not_infiniteDimensional_iff` / 引理 `SetRel.not_infiniteDimensional_iff`

English:
lemma SetRel.not_infiniteDimensional_iff
  given: [Nonempty α]
  proof: by
  rw [← not_finiteDimensional_iff]; rw [not_not]

中文:
引理 SetRel.not_infiniteDimensional_iff
  条件: [非空 α]
  证明: by
  rw [← not_finiteDimensional_iff]; rw [not_not]

Depends on / 依赖: not_finiteDimensional_iff, not_not
-/
lemma SetRel.not_infiniteDimensional_iff [Nonempty α] :
    ¬ r.InfiniteDimensional ↔ r.FiniteDimensional := by
  rw [← not_finiteDimensional_iff]; rw [not_not]

/--
lemma `SetRel.finiteDimensional_or_infiniteDimensional` / 引理 `SetRel.finiteDimensional_or_infiniteDimensional`

English:
lemma SetRel.finiteDimensional_or_infiniteDimensional
  given: [Nonempty α]
  proof: by
  rw [← not_finiteDimensional_iff]
  exact em r.FiniteDimensional

中文:
引理 SetRel.finiteDimensional_or_infiniteDimensional
  条件: [非空 α]
  证明: by
  rw [← not_finiteDimensional_iff]
  exact em r.FiniteDimensional

Depends on / 依赖: FiniteDimensional, not_finiteDimensional_iff, r.FiniteDimensional
-/
lemma SetRel.finiteDimensional_or_infiniteDimensional [Nonempty α] :
    r.FiniteDimensional ∨ r.InfiniteDimensional := by
  rw [← not_finiteDimensional_iff]
  exact em r.FiniteDimensional

/--
Instance `SetRel.FiniteDimensional.inv` / 实例 `SetRel.FiniteDimensional.inv`

English:
instance SetRel.FiniteDimensional.inv
  signature: [FiniteDimensional r]
  body: ⟨.reverse (.longestOf r), fun s => s.reverse.length_le_length_longestOf r⟩

中文:
实例 SetRel.有限维.inv
  签名: [有限维 r]
  定义体: ⟨.reverse (.longestOf r), fun s => s.reverse.length_le_length_longestOf r⟩

Depends on / 依赖: length_le_length_longestOf, longestOf, reverse, s.reverse.length_le_length_longestOf
-/
instance SetRel.FiniteDimensional.inv [FiniteDimensional r] : FiniteDimensional r.inv :=
  ⟨.reverse (.longestOf r), fun s => s.reverse.length_le_length_longestOf r⟩

variable {r} in
@[simp]
/--
lemma `SetRel.finiteDimensional_inv` / 引理 `SetRel.finiteDimensional_inv`

English:
lemma SetRel.finiteDimensional_inv
  statement: FiniteDimensional r.inv ↔ FiniteDimensional r
  proof: ⟨fun _ => .inv r.inv, fun _ => .inv _⟩

中文:
引理 SetRel.finiteDimensional_inv
  结论: 有限维 r.inv ↔ 有限维 r
  证明: ⟨fun _ => .inv r.inv, fun _ => .inv _⟩

Depends on / 依赖: r.inv
-/
lemma SetRel.finiteDimensional_inv : FiniteDimensional r.inv ↔ FiniteDimensional r :=
  ⟨fun _ => .inv r.inv, fun _ => .inv _⟩

/--
Instance `SetRel.InfiniteDimensional.inv` / 实例 `SetRel.InfiniteDimensional.inv`

English:
instance SetRel.InfiniteDimensional.inv
  signature: [InfiniteDimensional r]
  body: ⟨fun n => ⟨.reverse (.withLength r n), RelSeries.length_withLength r n⟩⟩

中文:
实例 SetRel.无限维.inv
  签名: [无限维 r]
  定义体: ⟨fun n => ⟨.reverse (.withLength r n), RelSeries.length_withLength r n⟩⟩

Depends on / 依赖: RelSeries, RelSeries.length_withLength, length_withLength, reverse, withLength
-/
instance SetRel.InfiniteDimensional.inv [InfiniteDimensional r] : InfiniteDimensional r.inv :=
  ⟨fun n => ⟨.reverse (.withLength r n), RelSeries.length_withLength r n⟩⟩

variable {r} in
@[simp]
/--
lemma `SetRel.infiniteDimensional_inv` / 引理 `SetRel.infiniteDimensional_inv`

English:
lemma SetRel.infiniteDimensional_inv
  statement: InfiniteDimensional r.inv ↔ InfiniteDimensional r
  proof: ⟨fun _ => .inv r.inv, fun _ => .inv _⟩

中文:
引理 SetRel.infiniteDimensional_inv
  结论: 无限维 r.inv ↔ 无限维 r
  证明: ⟨fun _ => .inv r.inv, fun _ => .inv _⟩

Depends on / 依赖: r.inv
-/
lemma SetRel.infiniteDimensional_inv : InfiniteDimensional r.inv ↔ InfiniteDimensional r :=
  ⟨fun _ => .inv r.inv, fun _ => .inv _⟩

/--
lemma `SetRel.IsWellFounded.inv_of_finiteDimensional` / 引理 `SetRel.IsWellFounded.inv_of_finiteDimensional`

English:
lemma SetRel.IsWellFounded.inv_of_finiteDimensional
  given: [r.FiniteDimensional]
  proof: by
  rw [IsWellFounded]; rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨f, hf⟩ => ?_⟩
  let s := RelSeries.mk (r := r) ((RelSeries.longestOf r).length + 1) (f ·) (hf ·)
  exact (RelSeries.longestOf r).length.lt_succ_self.not_ge s.length_le_length_longestOf

中文:
引理 SetRel.是良基.inv_of_finiteDimensional
  条件: [r.有限维]
  证明: by
  rw [IsWellFounded]; rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨f, hf⟩ => ?_⟩
  let s := RelSeries.mk (r := r) ((RelSeries.longestOf r).length + 1) (f ·) (hf ·)
  exact (RelSeries.longestOf r).length.lt_succ_self.not_ge s.length_le_length_longestOf

Depends on / 依赖: IsWellFounded, RelSeries, RelSeries.longestOf, RelSeries.mk, length, length.lt_succ_self.not_ge, length_le_length_longestOf, longestOf, lt_succ_self, not_ge, s.length_le_length_longestOf, wellFounded_iff_isEmpty_descending_chain
-/
lemma SetRel.IsWellFounded.inv_of_finiteDimensional [r.FiniteDimensional] :
    r.inv.IsWellFounded := by
  rw [IsWellFounded]; rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨f, hf⟩ => ?_⟩
  let s := RelSeries.mk (r := r) ((RelSeries.longestOf r).length + 1) (f ·) (hf ·)
  exact (RelSeries.longestOf r).length.lt_succ_self.not_ge s.length_le_length_longestOf

/--
lemma `SetRel.IsWellFounded.of_finiteDimensional` / 引理 `SetRel.IsWellFounded.of_finiteDimensional`

English:
lemma SetRel.IsWellFounded.of_finiteDimensional
  given: [r.FiniteDimensional]
  statement: r.IsWellFounded
  proof: .inv_of_finiteDimensional r.inv

中文:
引理 SetRel.是良基.of_finiteDimensional
  条件: [r.有限维]
  结论: r.是良基
  证明: .inv_of_finiteDimensional r.inv

Depends on / 依赖: inv_of_finiteDimensional, r.inv
-/
lemma SetRel.IsWellFounded.of_finiteDimensional [r.FiniteDimensional] : r.IsWellFounded :=
  .inv_of_finiteDimensional r.inv

/--
Definition of `FiniteDimensionalOrder` / `FiniteDimensionalOrder` 的定义

English:
abbreviation FiniteDimensionalOrder
  signature: (γ : Type*) [Preorder γ]
  body: SetRel.FiniteDimensional {(a, b) : γ × γ | a < b}

中文:
缩写 FiniteDimensionalOrder
  签名: (γ : 类型) [预序 γ]
  定义体: SetRel.FiniteDimensional {(a, b) : γ × γ | a < b}

Depends on / 依赖: FiniteDimensional, SetRel, SetRel.FiniteDimensional
-/
abbrev FiniteDimensionalOrder (γ : Type*) [Preorder γ] :=
  SetRel.FiniteDimensional {(a, b) : γ × γ | a < b}

/--
Instance `FiniteDimensionalOrder.ofUnique` / 实例 `FiniteDimensionalOrder.ofUnique`

English:
instance FiniteDimensionalOrder.ofUnique
  signature: (γ : Type*) [Preorder γ] [Unique γ]
  body: ⟨.singleton _ default, fun x => by
    by_contra! r
exact (x.step ⟨0, by lia⟩).ne Subsingleton.elim _ _⟩

中文:
实例 FiniteDimensionalOrder.ofUnique
  签名: (γ : 类型) [预序 γ] [唯一 γ]
  定义体: ⟨.singleton _ default, fun x => by
    by_contra! r
exact (x.step ⟨0, by lia⟩).ne Subsingleton.elim _ _⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, singleton, x.step
-/
instance FiniteDimensionalOrder.ofUnique (γ : Type*) [Preorder γ] [Unique γ] :
    FiniteDimensionalOrder γ where
  exists_longest_relSeries := ⟨.singleton _ default, fun x => by
    by_contra! r
exact (x.step ⟨0, by lia⟩).ne Subsingleton.elim _ _⟩

/--
Definition of `InfiniteDimensionalOrder` / `InfiniteDimensionalOrder` 的定义

English:
abbreviation InfiniteDimensionalOrder
  signature: (γ : Type*) [Preorder γ]
  body: SetRel.InfiniteDimensional {(a, b) : γ × γ | a < b}

中文:
缩写 InfiniteDimensionalOrder
  签名: (γ : 类型) [预序 γ]
  定义体: SetRel.InfiniteDimensional {(a, b) : γ × γ | a < b}

Depends on / 依赖: InfiniteDimensional, SetRel, SetRel.InfiniteDimensional
-/
abbrev InfiniteDimensionalOrder (γ : Type*) [Preorder γ] :=
  SetRel.InfiniteDimensional {(a, b) : γ × γ | a < b}

section LTSeries

variable (α) [Preorder α] [Preorder β]
/--
Definition of `LTSeries` / `LTSeries` 的定义

English:
abbreviation LTSeries
  body: RelSeries {(a, b) : α × α | a < b}

中文:
缩写 LTSeries
  定义体: RelSeries {(a, b) : α × α | a < b}

Depends on / 依赖: RelSeries
-/
abbrev LTSeries := RelSeries {(a, b) : α × α | a < b}

namespace LTSeries

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def longestOf [FiniteDimensionalOrder α]
  body: RelSeries.longestOf _

中文:
定义 noncomputable
  签名: def longestOf [FiniteDimensionalOrder α]
  定义体: RelSeries.longestOf _
-/
protected noncomputable def longestOf [FiniteDimensionalOrder α] : LTSeries α :=
  RelSeries.longestOf _

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def withLength [InfiniteDimensionalOrder α] (n : Nat)
  body: RelSeries.withLength _ n

中文:
定义 noncomputable
  签名: def withLength [InfiniteDimensionalOrder α] (n : 自然数)
  定义体: RelSeries.withLength _ n
-/
protected noncomputable def withLength [InfiniteDimensionalOrder α] (n : Nat) : LTSeries α :=
  RelSeries.withLength _ n

/--
lemma `length_withLength` / 引理 `length_withLength`

English:
lemma length_withLength
  given: [InfiniteDimensionalOrder α] (n : Nat)
  proof: RelSeries.length_withLength _ _

中文:
引理 length_withLength
  条件: [InfiniteDimensionalOrder α] (n : 自然数)
  证明: RelSeries.length_withLength _ _
-/
@[simp] lemma length_withLength [InfiniteDimensionalOrder α] (n : Nat) :
    (LTSeries.withLength α n).length = n :=
  RelSeries.length_withLength _ _

/--
lemma `nonempty_of_infiniteDimensionalOrder` / 引理 `nonempty_of_infiniteDimensionalOrder`

English:
lemma nonempty_of_infiniteDimensionalOrder
  given: [InfiniteDimensionalOrder α]
  statement: Nonempty α
  proof: ⟨LTSeries.withLength α 0 0⟩

中文:
引理 nonempty_of_infiniteDimensionalOrder
  条件: [InfiniteDimensionalOrder α]
  结论: 非空 α
  证明: ⟨LTSeries.withLength α 0 0⟩

Depends on / 依赖: LTSeries, LTSeries.withLength, withLength
-/
lemma nonempty_of_infiniteDimensionalOrder [InfiniteDimensionalOrder α] : Nonempty α :=
  ⟨LTSeries.withLength α 0 0⟩

/--
lemma `nonempty_of_finiteDimensionalOrder` / 引理 `nonempty_of_finiteDimensionalOrder`

English:
lemma nonempty_of_finiteDimensionalOrder
  given: [FiniteDimensionalOrder α]
  statement: Nonempty α
  proof: by
  obtain ⟨p, _⟩ := (SetRel.finiteDimensional_iff _).mp ‹_›
  exact ⟨p 0⟩

中文:
引理 nonempty_of_finiteDimensionalOrder
  条件: [FiniteDimensionalOrder α]
  结论: 非空 α
  证明: by
  obtain ⟨p, _⟩ := (SetRel.finiteDimensional_iff _).mp ‹_›
  exact ⟨p 0⟩

Depends on / 依赖: SetRel, SetRel.finiteDimensional_iff, finiteDimensional_iff
-/
lemma nonempty_of_finiteDimensionalOrder [FiniteDimensionalOrder α] : Nonempty α := by
  obtain ⟨p, _⟩ := (SetRel.finiteDimensional_iff _).mp ‹_›
  exact ⟨p 0⟩

variable {α}

/--
lemma `longestOf_is_longest` / 引理 `longestOf_is_longest`

English:
lemma longestOf_is_longest
  given: [FiniteDimensionalOrder α] (x : LTSeries α)
  proof: RelSeries.length_le_length_longestOf _ _

中文:
引理 longestOf_is_longest
  条件: [FiniteDimensionalOrder α] (x : LTSeries α)
  证明: RelSeries.length_le_length_longestOf _ _

Depends on / 依赖: RelSeries, RelSeries.length_le_length_longestOf, length_le_length_longestOf
-/
lemma longestOf_is_longest [FiniteDimensionalOrder α] (x : LTSeries α) :
    x.length <= (LTSeries.longestOf α).length :=
  RelSeries.length_le_length_longestOf _ _

/--
lemma `longestOf_len_unique` / 引理 `longestOf_len_unique`

English:
lemma longestOf_len_unique
  statement: [FiniteDimensionalOrder α] (p : LTSeries α)
  proof: le_antisymm (longestOf_is_longest _) (is_longest _)

中文:
引理 longestOf_len_unique
  结论: [FiniteDimensionalOrder α] (p : LTSeries α)
  证明: le_antisymm (longestOf_is_longest _) (is_longest _)

Depends on / 依赖: is_longest, le_antisymm, longestOf_is_longest
-/
lemma longestOf_len_unique [FiniteDimensionalOrder α] (p : LTSeries α)
    (is_longest : forall (q : LTSeries α), q.length <= p.length) :
    p.length = (LTSeries.longestOf α).length :=
  le_antisymm (longestOf_is_longest _) (is_longest _)


/--
lemma `strictMono` / 引理 `strictMono`

English:
lemma strictMono
  given: (x : LTSeries α)
  statement: StrictMono x
  proof: fun _ _ h => x.rel_of_lt h

中文:
引理 strictMono
  条件: (x : LTSeries α)
  结论: 严格递增 x
  证明: fun _ _ h => x.rel_of_lt h

Depends on / 依赖: of_isLocalizationAway, rel_of_lt, x.rel_of_lt
-/
lemma strictMono (x : LTSeries α) : StrictMono x :=
  fun _ _ h => x.rel_of_lt h

/--
lemma `monotone` / 引理 `monotone`

English:
lemma monotone
  given: (x : LTSeries α)
  statement: Monotone x
  proof: x.strictMono.monotone

中文:
引理 monotone
  条件: (x : LTSeries α)
  结论: 递增 x
  证明: x.strictMono.monotone

Depends on / 依赖: monotone, strictMono, x.strictMono.monotone
-/
lemma monotone (x : LTSeries α) : Monotone x :=
  x.strictMono.monotone

/--
lemma `head_le` / 引理 `head_le`

English:
lemma head_le
  given: (x : LTSeries α) (n : Fin (x.length + 1))
  statement: x.head <= x n
  proof: x.monotone (Fin.zero_le n)

中文:
引理 head_le
  条件: (x : LTSeries α) (n : 有限集 (x.length + 1))
  结论: x.head <= x n
  证明: x.monotone (Fin.zero_le n)

Depends on / 依赖: Fin.zero_le, monotone, x.monotone, zero_le
-/
lemma head_le (x : LTSeries α) (n : Fin (x.length + 1)) : x.head <= x n :=
  x.monotone (Fin.zero_le n)

/--
lemma `head_le_last` / 引理 `head_le_last`

English:
lemma head_le_last
  given: (x : LTSeries α)
  statement: x.head <= x.last
  proof: x.head_le _

中文:
引理 head_le_last
  条件: (x : LTSeries α)
  结论: x.head <= x.last
  证明: x.head_le _

Depends on / 依赖: head_le, x.head_le
-/
lemma head_le_last (x : LTSeries α) : x.head <= x.last := x.head_le _

/-- An alternative constructor of `LTSeries` from a strictly monotone function. -/
@[simps]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (length : Nat) (toFun : Fin (length + 1) -> α) (strictMono : StrictMono toFun)
  body: length
  toFun := toFun
step i := strictMono lt_add_one i.1

中文:
定义 mk
  签名: (length : 自然数) (toFun : 有限集 (length + 1) -> α) (strictMono : 严格递增 toFun)
  定义体: length
  toFun := toFun
step i := strictMono lt_add_one i.1

Depends on / 依赖: length
-/
def mk (length : Nat) (toFun : Fin (length + 1) -> α) (strictMono : StrictMono toFun) :
    LTSeries α where
  length := length
  toFun := toFun
step i := strictMono lt_add_one i.1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `injStrictMono` / `injStrictMono` 的定义

English:
definition injStrictMono
  signature: (n : Nat)
  body: mk f.1.1 f.1.2 f.2
  inj' f g e := by
    obtain ⟨⟨lf, f⟩, mf⟩ := f
    obtain ⟨⟨lg, g⟩, mg⟩ := g
    dsimp only at mf mg e
    have leq := congr($(e).length)
    rw [mk_length lf f mf]; rw [mk_length lg g mg]; rw [Fin.val_eq_val] at leq
    subst leq
    simp_rw [Subtype.mk_eq_mk, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    have feq := fun i => congr($(e).toFun i)
    simp_rw [mk_toFun lf f mf, mk_toFun lf g mg, mk_length lf f mf] at feq
    rwa [funext_iff]

中文:
定义 injStrictMono
  签名: (n : 自然数)
  定义体: mk f.1.1 f.1.2 f.2
  inj' f g e := by
    obtain ⟨⟨lf, f⟩, mf⟩ := f
    obtain ⟨⟨lg, g⟩, mg⟩ := g
    dsimp only at mf mg e
    have leq := congr($(e).length)
    rw [mk_length lf f mf]; rw [mk_length lg g mg]; rw [Fin.val_eq_val] at leq
    subst leq
    simp_rw [Subtype.mk_eq_mk, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    have feq := fun i => congr($(e).toFun i)
    simp_rw [mk_toFun lf f mf, mk_toFun lf g mg, mk_length lf f mf] at feq
    rwa [funext_iff]
-/
def injStrictMono (n : Nat) :
    {f : (l : Fin n) × (Fin (l + 1) -> α) // StrictMono f.2} ↪ LTSeries α where
  toFun f := mk f.1.1 f.1.2 f.2
  inj' f g e := by
    obtain ⟨⟨lf, f⟩, mf⟩ := f
    obtain ⟨⟨lg, g⟩, mg⟩ := g
    dsimp only at mf mg e
    have leq := congr($(e).length)
    rw [mk_length lf f mf]; rw [mk_length lg g mg]; rw [Fin.val_eq_val] at leq
    subst leq
    simp_rw [Subtype.mk_eq_mk, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    have feq := fun i => congr($(e).toFun i)
    simp_rw [mk_toFun lf f mf, mk_toFun lf g mg, mk_length lf f mf] at feq
    rwa [funext_iff]

/--
For two preorders `α, β`, if `f : α → β` is strictly monotonic, then a strict chain of `α`
can be pushed out to a strict chain of `β` by
`a₀ < a₁ < ... < aₙ ↦ f a₀ < f a₁ < ... < f aₙ`
-/
@[simps!]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (p : LTSeries α) (f : α -> β) (hf : StrictMono f)
  body: LTSeries.mk p.length (f.comp p) (hf.comp p.strictMono)

中文:
定义 map
  签名: (p : LTSeries α) (f : α -> β) (hf : 严格递增 f)
  定义体: LTSeries.mk p.length (f.comp p) (hf.comp p.strictMono)

Depends on / 依赖: LTSeries, LTSeries.mk, f.comp, hf.comp, length, p.length, p.strictMono, strictMono
-/
def map (p : LTSeries α) (f : α -> β) (hf : StrictMono f) : LTSeries β :=
  LTSeries.mk p.length (f.comp p) (hf.comp p.strictMono)

/--
lemma `head_map` / 引理 `head_map`

English:
lemma head_map
  given: (p : LTSeries α) (f : α -> β) (hf : StrictMono f)
  proof: rfl

中文:
引理 head_map
  条件: (p : LTSeries α) (f : α -> β) (hf : 严格递增 f)
  证明: rfl
-/
@[simp] lemma head_map (p : LTSeries α) (f : α -> β) (hf : StrictMono f) :
    (p.map f hf).head = f p.head := rfl

/--
lemma `last_map` / 引理 `last_map`

English:
lemma last_map
  given: (p : LTSeries α) (f : α -> β) (hf : StrictMono f)
  proof: rfl

中文:
引理 last_map
  条件: (p : LTSeries α) (f : α -> β) (hf : 严格递增 f)
  证明: rfl
-/
@[simp] lemma last_map (p : LTSeries α) (f : α -> β) (hf : StrictMono f) :
    (p.map f hf).last = f p.last := rfl

/--
For two preorders `α, β`, if `f : α → β` is surjective and strictly comonotonic, then a
strict series of `β` can be pulled back to a strict chain of `α` by
`b₀ < b₁ < ... < bₙ ↦ f⁻¹ b₀ < f⁻¹ b₁ < ... < f⁻¹ bₙ` where `f⁻¹ bᵢ` is an arbitrary element in the
preimage of `f⁻¹ {bᵢ}`.
-/
@[simps!]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (p : LTSeries β) (f : α -> β)
  body: mk p.length (fun i => (surjective (p i)).choose)
    (fun i j h => comap (by simpa only [(surjective _).choose_spec] using p.strictMono h))

中文:
定义 comap
  签名: (p : LTSeries β) (f : α -> β)
  定义体: mk p.length (fun i => (surjective (p i)).choose)
    (fun i j h => comap (by simpa only [(surjective _).choose_spec] using p.strictMono h))

Depends on / 依赖: choose_spec, length, p.length, p.strictMono, strictMono, surjective
-/
noncomputable def comap (p : LTSeries β) (f : α -> β)
    (comap : forall ⦃x y⦄, f x < f y -> x < y)
    (surjective : Function.Surjective f) :
    LTSeries α :=
  mk p.length (fun i => (surjective (p i)).choose)
    (fun i j h => comap (by simpa only [(surjective _).choose_spec] using p.strictMono h))

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (n : Nat)
  body: n
  toFun := fun i => i
  step i := Nat.lt_add_one i

中文:
定义 range
  签名: (n : 自然数)
  定义体: n
  toFun := fun i => i
  step i := Nat.lt_add_one i
-/
def range (n : Nat) : LTSeries Nat where
  length := n
  toFun := fun i => i
  step i := Nat.lt_add_one i

/--
lemma `length_range` / 引理 `length_range`

English:
lemma length_range
  given: (n : Nat)
  statement: (range n).length = n
  proof: rfl

中文:
引理 length_range
  条件: (n : 自然数)
  结论: (range n).length = n
  证明: rfl
-/
@[simp] lemma length_range (n : Nat) : (range n).length = n := rfl

/--
lemma `range_apply` / 引理 `range_apply`

English:
lemma range_apply
  given: (n : Nat) (i : Fin (n + 1))
  statement: (range n) i = i
  proof: rfl

中文:
引理 range_apply
  条件: (n : 自然数) (i : 有限集 (n + 1))
  结论: (range n) i = i
  证明: rfl
-/
@[simp] lemma range_apply (n : Nat) (i : Fin (n + 1)) : (range n) i = i := rfl

/--
lemma `head_range` / 引理 `head_range`

English:
lemma head_range
  given: (n : Nat)
  statement: (range n).head = 0
  proof: rfl

中文:
引理 head_range
  条件: (n : 自然数)
  结论: (range n).head = 0
  证明: rfl
-/
@[simp] lemma head_range (n : Nat) : (range n).head = 0 := rfl

/--
lemma `last_range` / 引理 `last_range`

English:
lemma last_range
  given: (n : Nat)
  statement: (range n).last = n
  proof: rfl

中文:
引理 last_range
  条件: (n : 自然数)
  结论: (range n).last = n
  证明: rfl
-/
@[simp] lemma last_range (n : Nat) : (range n).last = n := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_relSeries_covBy` / 定理 `exists_relSeries_covBy`

English:
theorem exists_relSeries_covBy
  proof: by
  obtain ⟨n, s, h⟩ := s
  induction n with
  | zero => exact ⟨⟨0, s, nofun⟩, (Equiv.refl _).toEmbedding, rfl, rfl, rfl⟩
  | succ n IH =>
    obtain ⟨t₁, i, ht, hi₁, hi₂⟩ := IH (s ∘ Fin.castSucc) fun _ => h _
    obtain ⟨t₂, h₁, m, h₂, ht₂⟩ :=
      exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le (h (.last _)).le
    let t₃ : RelSeries {(a, b) : α × α | a ⋖ b} := ⟨m, (t₂ ·), fun i => by simpa using! ht₂ i⟩
    have H : t₁.last = t₂ 0 := (congr(t₁ $hi₂.symm).trans (congr_fun ht _)).trans h₁.symm
    refine ⟨t₁.smash t₃ H, ⟨Fin.snoc (Fin.castLE (by simp) ∘ i) (.last _), ?_⟩, ?_, ?_, ?_⟩
    · refine Fin.lastCases (Fin.lastCases (fun _ => rfl) fun j eq => ?_) fun j => Fin.lastCases
        (fun eq => ?_) fun k eq => Fin.ext (congr_arg Fin.val (by simpa using! eq) :)
      on_goal 2 => rw [eq_comm] at eq
      all_goals
        rw [Fin.snoc_castSucc] at eq
        obtain rfl : m = 0 := by simpa [t₃] using! (congr_arg Fin.val eq).trans_lt (i j).2
        cases (h (.last _)).ne' (h₂.symm.trans h₁)
    · refine funext (Fin.lastCases ?_ fun j => ?_)
      · convert! h₂; simpa using! RelSeries.last_smash ..
      convert! congr_fun ht j using 1
      simp [RelSeries.smash_castLE]
    all_goals simp [Fin.snoc, Fin.castPred_zero, hi₁]

中文:
定理 存在_relSeries_covBy
  证明: by
  obtain ⟨n, s, h⟩ := s
  induction n with
  | zero => exact ⟨⟨0, s, nofun⟩, (Equiv.refl _).toEmbedding, rfl, rfl, rfl⟩
  | succ n IH =>
    obtain ⟨t₁, i, ht, hi₁, hi₂⟩ := IH (s ∘ Fin.castSucc) fun _ => h _
    obtain ⟨t₂, h₁, m, h₂, ht₂⟩ :=
      exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le (h (.last _)).le
    let t₃ : RelSeries {(a, b) : α × α | a ⋖ b} := ⟨m, (t₂ ·), fun i => by simpa using! ht₂ i⟩
    have H : t₁.last = t₂ 0 := (congr(t₁ $hi₂.symm).trans (congr_fun ht _)).trans h₁.symm
    refine ⟨t₁.smash t₃ H, ⟨Fin.snoc (Fin.castLE (by simp) ∘ i) (.last _), ?_⟩, ?_, ?_, ?_⟩
    · refine Fin.lastCases (Fin.lastCases (fun _ => rfl) fun j eq => ?_) fun j => Fin.lastCases
        (fun eq => ?_) fun k eq => Fin.ext (congr_arg Fin.val (by simpa using! eq) :)
      on_goal 2 => rw [eq_comm] at eq
      all_goals
        rw [Fin.snoc_castSucc] at eq
        obtain rfl : m = 0 := by simpa [t₃] using! (congr_arg Fin.val eq).trans_lt (i j).2
        cases (h (.last _)).ne' (h₂.symm.trans h₁)
    · refine funext (Fin.lastCases ?_ fun j => ?_)
      · convert! h₂; simpa using! RelSeries.last_smash ..
      convert! congr_fun ht j using 1
      simp [RelSeries.smash_castLE]
    all_goals simp [Fin.snoc, Fin.castPred_zero, hi₁]

Depends on / 依赖: Equiv.refl, Fin.castSucc, RelSeries, castSucc, congr_fun, exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le, toEmbedding
-/
theorem exists_relSeries_covBy
    {α} [PartialOrder α] [WellFoundedLT α] [WellFoundedGT α] (s : LTSeries α) :
    exists (t : RelSeries {(a, b) : α × α | a ⋖ b}) (i : Fin (s.length + 1) ↪ Fin (t.length + 1)),
      t ∘ i = s ∧ i 0 = 0 ∧ i (.last _) = .last _ := by
  obtain ⟨n, s, h⟩ := s
  induction n with
  | zero => exact ⟨⟨0, s, nofun⟩, (Equiv.refl _).toEmbedding, rfl, rfl, rfl⟩
  | succ n IH =>
    obtain ⟨t₁, i, ht, hi₁, hi₂⟩ := IH (s ∘ Fin.castSucc) fun _ => h _
    obtain ⟨t₂, h₁, m, h₂, ht₂⟩ :=
      exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le (h (.last _)).le
    let t₃ : RelSeries {(a, b) : α × α | a ⋖ b} := ⟨m, (t₂ ·), fun i => by simpa using! ht₂ i⟩
    have H : t₁.last = t₂ 0 := (congr(t₁ $hi₂.symm).trans (congr_fun ht _)).trans h₁.symm
    refine ⟨t₁.smash t₃ H, ⟨Fin.snoc (Fin.castLE (by simp) ∘ i) (.last _), ?_⟩, ?_, ?_, ?_⟩
    · refine Fin.lastCases (Fin.lastCases (fun _ => rfl) fun j eq => ?_) fun j => Fin.lastCases
        (fun eq => ?_) fun k eq => Fin.ext (congr_arg Fin.val (by simpa using! eq) :)
      on_goal 2 => rw [eq_comm] at eq
      all_goals
        rw [Fin.snoc_castSucc] at eq
        obtain rfl : m = 0 := by simpa [t₃] using! (congr_arg Fin.val eq).trans_lt (i j).2
        cases (h (.last _)).ne' (h₂.symm.trans h₁)
    · refine funext (Fin.lastCases ?_ fun j => ?_)
      · convert! h₂; simpa using! RelSeries.last_smash ..
      convert! congr_fun ht j using 1
      simp [RelSeries.smash_castLE]
    all_goals simp [Fin.snoc, Fin.castPred_zero, hi₁]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot` / 定理 `exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot`

English:
theorem exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
  proof: by
  wlog h₁ : s.head = ⊥
  · obtain ⟨t, i, hi, ht⟩ := this (s.cons ⊥ (bot_lt_iff_ne_bot.mpr h₁)) rfl
    exact ⟨t, ⟨fun j => i (j.succ.cast (by simp)), fun _ _ => by simp⟩,
      funext fun j => (congr_fun hi _).trans (RelSeries.cons_cast_succ _ _ _ _), ht⟩
  wlog h₂ : s.last = ⊤
  · obtain ⟨t, i, hi, ht⟩ := this (s.snoc ⊤ (lt_top_iff_ne_top.mpr h₂)) (by simp [h₁]) (by simp)
    exact ⟨t, ⟨fun j => i (.cast (by simp) j.castSucc), fun _ _ => by simp⟩,
      funext fun j => (congr_fun hi _).trans (RelSeries.snoc_cast_castSucc _ _ _ _), ht⟩
  obtain ⟨t, i, hit, hi₁, hi₂⟩ := s.exists_relSeries_covBy
  refine ⟨t, i, hit, ?_, ?_⟩
  · rw [← h₁, RelSeries.head, RelSeries.head, ← hi₁, ← hit, Function.comp]
  · rw [← h₂, RelSeries.last, RelSeries.last, ← hi₂, ← hit, Function.comp]

中文:
定理 存在_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
  证明: by
  wlog h₁ : s.head = ⊥
  · obtain ⟨t, i, hi, ht⟩ := this (s.cons ⊥ (bot_lt_iff_ne_bot.mpr h₁)) rfl
    exact ⟨t, ⟨fun j => i (j.succ.cast (by simp)), fun _ _ => by simp⟩,
      funext fun j => (congr_fun hi _).trans (RelSeries.cons_cast_succ _ _ _ _), ht⟩
  wlog h₂ : s.last = ⊤
  · obtain ⟨t, i, hi, ht⟩ := this (s.snoc ⊤ (lt_top_iff_ne_top.mpr h₂)) (by simp [h₁]) (by simp)
    exact ⟨t, ⟨fun j => i (.cast (by simp) j.castSucc), fun _ _ => by simp⟩,
      funext fun j => (congr_fun hi _).trans (RelSeries.snoc_cast_castSucc _ _ _ _), ht⟩
  obtain ⟨t, i, hit, hi₁, hi₂⟩ := s.exists_relSeries_covBy
  refine ⟨t, i, hit, ?_, ?_⟩
  · rw [← h₁, RelSeries.head, RelSeries.head, ← hi₁, ← hit, Function.comp]
  · rw [← h₂, RelSeries.last, RelSeries.last, ← hi₂, ← hit, Function.comp]

Depends on / 依赖: RelSeries, RelSeries.cons_cast_succ, RelSeries.snoc_cast_castSu, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, castSucc, congr_fun, cons_cast_succ, j.castSucc, j.succ.cast, lt_top_iff_ne_top, lt_top_iff_ne_top.mpr, s.cons, s.head, s.last, s.snoc, snoc_cast_castSu
-/
theorem exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
    {α} [PartialOrder α] [BoundedOrder α] [WellFoundedLT α] [WellFoundedGT α] (s : LTSeries α) :
    exists (t : RelSeries {(a, b) : α × α | a ⋖ b}) (i : Fin (s.length + 1) ↪ Fin (t.length + 1)),
      t ∘ i = s ∧ t.head = ⊥ ∧ t.last = ⊤ := by
  wlog h₁ : s.head = ⊥
  · obtain ⟨t, i, hi, ht⟩ := this (s.cons ⊥ (bot_lt_iff_ne_bot.mpr h₁)) rfl
    exact ⟨t, ⟨fun j => i (j.succ.cast (by simp)), fun _ _ => by simp⟩,
      funext fun j => (congr_fun hi _).trans (RelSeries.cons_cast_succ _ _ _ _), ht⟩
  wlog h₂ : s.last = ⊤
  · obtain ⟨t, i, hi, ht⟩ := this (s.snoc ⊤ (lt_top_iff_ne_top.mpr h₂)) (by simp [h₁]) (by simp)
    exact ⟨t, ⟨fun j => i (.cast (by simp) j.castSucc), fun _ _ => by simp⟩,
      funext fun j => (congr_fun hi _).trans (RelSeries.snoc_cast_castSucc _ _ _ _), ht⟩
  obtain ⟨t, i, hit, hi₁, hi₂⟩ := s.exists_relSeries_covBy
  refine ⟨t, i, hit, ?_, ?_⟩
  · rw [← h₁, RelSeries.head, RelSeries.head, ← hi₁, ← hit, Function.comp]
  · rw [← h₂, RelSeries.last, RelSeries.last, ← hi₂, ← hit, Function.comp]

/--
lemma `apply_add_index_le_apply_add_index_nat` / 引理 `apply_add_index_le_apply_add_index_nat`

English:
lemma apply_add_index_le_apply_add_index_nat
  statement: (p : LTSeries Nat) (i j : Fin (p.length + 1))
  proof: by
  have ⟨i, hi⟩ := i
  have ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  simp only at *
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _hij ih =>
    specialize ih (Nat.lt_of_succ_lt hj)
    have step : p ⟨j, _⟩ < p ⟨j + 1, _⟩ := p.step ⟨j, by lia⟩
    lia

中文:
引理 apply_add_index_le_apply_add_index_nat
  结论: (p : LTSeries 自然数) (i j : 有限集 (p.length + 1))
  证明: by
  have ⟨i, hi⟩ := i
  have ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  simp only at *
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _hij ih =>
    specialize ih (Nat.lt_of_succ_lt hj)
    have step : p ⟨j, _⟩ < p ⟨j + 1, _⟩ := p.step ⟨j, by lia⟩
    lia

Depends on / 依赖: Fin.mk_le_mk, Nat.le_induction, Nat.lt_of_succ_lt, _hij, le_induction, lt_of_succ_lt, mk_le_mk, p.step, specialize
-/
lemma apply_add_index_le_apply_add_index_nat (p : LTSeries Nat) (i j : Fin (p.length + 1))
    (hij : i <= j) : p i + j <= p j + i := by
  have ⟨i, hi⟩ := i
  have ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  simp only at *
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _hij ih =>
    specialize ih (Nat.lt_of_succ_lt hj)
    have step : p ⟨j, _⟩ < p ⟨j + 1, _⟩ := p.step ⟨j, by lia⟩
    lia

/--
lemma `apply_add_index_le_apply_add_index_int` / 引理 `apply_add_index_le_apply_add_index_int`

English:
lemma apply_add_index_le_apply_add_index_int
  statement: (p : LTSeries Int) (i j : Fin (p.length + 1))
  proof: by
  -- The proof is identical to `LTSeries.apply_add_index_le_apply_add_index_nat`, but seemed easier
  -- to copy rather than to abstract
  have ⟨i, hi⟩ := i
  have ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  simp only at *
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _hij ih =>
    specialize ih (Nat.lt_of_succ_lt hj)
    have step : p ⟨j, _⟩ < p ⟨j + 1, _⟩ := p.step ⟨j, by lia⟩
    lia

中文:
引理 apply_add_index_le_apply_add_index_int
  结论: (p : LTSeries 整数) (i j : 有限集 (p.length + 1))
  证明: by
  -- The proof is identical to `LTSeries.apply_add_index_le_apply_add_index_nat`, but seemed easier
  -- to copy rather than to abstract
  have ⟨i, hi⟩ := i
  have ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  simp only at *
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _hij ih =>
    specialize ih (Nat.lt_of_succ_lt hj)
    have step : p ⟨j, _⟩ < p ⟨j + 1, _⟩ := p.step ⟨j, by lia⟩
    lia
-/
lemma apply_add_index_le_apply_add_index_int (p : LTSeries Int) (i j : Fin (p.length + 1))
    (hij : i <= j) : p i + j <= p j + i := by
  -- The proof is identical to `LTSeries.apply_add_index_le_apply_add_index_nat`, but seemed easier
  -- to copy rather than to abstract
  have ⟨i, hi⟩ := i
  have ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  simp only at *
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _hij ih =>
    specialize ih (Nat.lt_of_succ_lt hj)
    have step : p ⟨j, _⟩ < p ⟨j + 1, _⟩ := p.step ⟨j, by lia⟩
    lia

/--
lemma `head_add_length_le_nat` / 引理 `head_add_length_le_nat`

English:
lemma head_add_length_le_nat
  given: (p : LTSeries Nat)
  statement: p.head + p.length <= p.last
  proof: LTSeries.apply_add_index_le_apply_add_index_nat _ _ (Fin.last _) (Fin.zero_le _)

中文:
引理 head_add_length_le_nat
  条件: (p : LTSeries 自然数)
  结论: p.head + p.length <= p.last
  证明: LTSeries.apply_add_index_le_apply_add_index_nat _ _ (Fin.last _) (Fin.zero_le _)

Depends on / 依赖: Fin.last, Fin.zero_le, LTSeries, LTSeries.apply_add_index_le_apply_add_index_nat, apply_add_index_le_apply_add_index_nat, zero_le
-/
lemma head_add_length_le_nat (p : LTSeries Nat) : p.head + p.length <= p.last :=
  LTSeries.apply_add_index_le_apply_add_index_nat _ _ (Fin.last _) (Fin.zero_le _)

/--
lemma `head_add_length_le_int` / 引理 `head_add_length_le_int`

English:
lemma head_add_length_le_int
  given: (p : LTSeries Int)
  statement: p.head + p.length <= p.last
  proof: by
  simpa using! LTSeries.apply_add_index_le_apply_add_index_int _ _ (Fin.last _) (Fin.zero_le _)

中文:
引理 head_add_length_le_int
  条件: (p : LTSeries 整数)
  结论: p.head + p.length <= p.last
  证明: by
  simpa using! LTSeries.apply_add_index_le_apply_add_index_int _ _ (Fin.last _) (Fin.zero_le _)

Depends on / 依赖: Fin.last, Fin.zero_le, LTSeries, LTSeries.apply_add_index_le_apply_add_index_int, apply_add_index_le_apply_add_index_int, zero_le
-/
lemma head_add_length_le_int (p : LTSeries Int) : p.head + p.length <= p.last := by
  simpa using! LTSeries.apply_add_index_le_apply_add_index_int _ _ (Fin.last _) (Fin.zero_le _)

section Fintype

variable [Fintype α]

/--
lemma `length_lt_card` / 引理 `length_lt_card`

English:
lemma length_lt_card
  given: (s : LTSeries α)
  statement: s.length < Fintype.card α
  proof: by
  by_contra! h
  obtain ⟨i, j, hn, he⟩ := Fintype.exists_ne_map_eq_of_card_lt s (by rw [Fintype.card_fin]; lia)
  wlog hl : i < j generalizing i j
  · exact this j i hn.symm he.symm (by lia)
  exact absurd he (s.strictMono hl).ne

中文:
引理 length_lt_card
  条件: (s : LTSeries α)
  结论: s.length < 有限类型.card α
  证明: by
  by_contra! h
  obtain ⟨i, j, hn, he⟩ := Fintype.exists_ne_map_eq_of_card_lt s (by rw [Fintype.card_fin]; lia)
  wlog hl : i < j generalizing i j
  · exact this j i hn.symm he.symm (by lia)
  exact absurd he (s.strictMono hl).ne

Depends on / 依赖: Fintype, Fintype.card_fin, Fintype.exists_ne_map_eq_of_card_lt, absurd, card_fin, exists_ne_map_eq_of_card_lt, generalizing, he.symm, hn.symm, s.strictMono, strictMono
-/
lemma length_lt_card (s : LTSeries α) : s.length < Fintype.card α := by
  by_contra! h
  obtain ⟨i, j, hn, he⟩ := Fintype.exists_ne_map_eq_of_card_lt s (by rw [Fintype.card_fin]; lia)
  wlog hl : i < j generalizing i j
  · exact this j i hn.symm he.symm (by lia)
  exact absurd he (s.strictMono hl).ne

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableLT
  signature: α] : Fintype (LTSeries α) where
  body: Finset.univ.map (injStrictMono (Fintype.card α))
  complete s := by
    have bl := s.length_lt_card
    obtain ⟨l, f, mf⟩ := s
    simp_rw [Finset.mem_map, Finset.mem_univ, true_and, Subtype.exists]
    use ⟨⟨l, bl⟩, f⟩, Fin.strictMono_iff_lt_succ.mpr mf; rfl

中文:
实例 [DecidableLT
  签名: α] : 有限类型 (LTSeries α) where
  定义体: Finset.univ.map (injStrictMono (Fintype.card α))
  complete s := by
    have bl := s.length_lt_card
    obtain ⟨l, f, mf⟩ := s
    simp_rw [Finset.mem_map, Finset.mem_univ, true_and, Subtype.exists]
    use ⟨⟨l, bl⟩, f⟩, Fin.strictMono_iff_lt_succ.mpr mf; rfl

Depends on / 依赖: Finset, Finset.univ.map, Fintype, Fintype.card, injStrictMono
-/
instance [DecidableLT α] : Fintype (LTSeries α) where
  elems := Finset.univ.map (injStrictMono (Fintype.card α))
  complete s := by
    have bl := s.length_lt_card
    obtain ⟨l, f, mf⟩ := s
    simp_rw [Finset.mem_map, Finset.mem_univ, true_and, Subtype.exists]
    use ⟨⟨l, bl⟩, f⟩, Fin.strictMono_iff_lt_succ.mpr mf; rfl

end Fintype

end LTSeries

end LTSeries

/--
lemma `not_finiteDimensionalOrder_iff` / 引理 `not_finiteDimensionalOrder_iff`

English:
lemma not_finiteDimensionalOrder_iff
  given: [Preorder α] [Nonempty α]
  proof: SetRel.not_finiteDimensional_iff

中文:
引理 not_finiteDimensionalOrder_iff
  条件: [预序 α] [非空 α]
  证明: SetRel.not_finiteDimensional_iff

Depends on / 依赖: SetRel, SetRel.not_finiteDimensional_iff, not_finiteDimensional_iff
-/
lemma not_finiteDimensionalOrder_iff [Preorder α] [Nonempty α] :
    ¬ FiniteDimensionalOrder α ↔ InfiniteDimensionalOrder α :=
  SetRel.not_finiteDimensional_iff

/--
lemma `not_infiniteDimensionalOrder_iff` / 引理 `not_infiniteDimensionalOrder_iff`

English:
lemma not_infiniteDimensionalOrder_iff
  given: [Preorder α] [Nonempty α]
  proof: SetRel.not_infiniteDimensional_iff

中文:
引理 not_infiniteDimensionalOrder_iff
  条件: [预序 α] [非空 α]
  证明: SetRel.not_infiniteDimensional_iff

Depends on / 依赖: SetRel, SetRel.not_infiniteDimensional_iff, not_infiniteDimensional_iff
-/
lemma not_infiniteDimensionalOrder_iff [Preorder α] [Nonempty α] :
    ¬ InfiniteDimensionalOrder α ↔ FiniteDimensionalOrder α :=
  SetRel.not_infiniteDimensional_iff

variable (α) in
/--
lemma `finiteDimensionalOrder_or_infiniteDimensionalOrder` / 引理 `finiteDimensionalOrder_or_infiniteDimensionalOrder`

English:
lemma finiteDimensionalOrder_or_infiniteDimensionalOrder
  given: [Preorder α] [Nonempty α]
  proof: SetRel.finiteDimensional_or_infiniteDimensional _

中文:
引理 finiteDimensionalOrder_or_infiniteDimensionalOrder
  条件: [预序 α] [非空 α]
  证明: SetRel.finiteDimensional_or_infiniteDimensional _

Depends on / 依赖: SetRel, SetRel.finiteDimensional_or_infiniteDimensional, finiteDimensional_or_infiniteDimensional
-/
lemma finiteDimensionalOrder_or_infiniteDimensionalOrder [Preorder α] [Nonempty α] :
    FiniteDimensionalOrder α ∨ InfiniteDimensionalOrder α :=
  SetRel.finiteDimensional_or_infiniteDimensional _

/--
lemma `infiniteDimensionalOrder_of_strictMono` / 引理 `infiniteDimensionalOrder_of_strictMono`

English:
lemma infiniteDimensionalOrder_of_strictMono
  statement: [Preorder α] [Preorder β]
  proof: ⟨fun n => ⟨(LTSeries.withLength _ n).map f hf, LTSeries.length_withLength α n⟩⟩

中文:
引理 infiniteDimensionalOrder_of_strictMono
  结论: [预序 α] [预序 β]
  证明: ⟨fun n => ⟨(LTSeries.withLength _ n).map f hf, LTSeries.length_withLength α n⟩⟩

Depends on / 依赖: LTSeries, LTSeries.length_withLength, LTSeries.withLength, length_withLength, withLength
-/
lemma infiniteDimensionalOrder_of_strictMono [Preorder α] [Preorder β]
    (f : α -> β) (hf : StrictMono f) [InfiniteDimensionalOrder α] :
    InfiniteDimensionalOrder β :=
  ⟨fun n => ⟨(LTSeries.withLength _ n).map f hf, LTSeries.length_withLength α n⟩⟩
