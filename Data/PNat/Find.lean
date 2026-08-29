/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Floris van Doorn
-/
module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.PNat.Basic

/-!
# Explicit least witnesses to existentials on positive natural numbers

Implemented via calling out to `Nat.find`.

-/

@[expose] public section


namespace PNat

variable {p q : Nat+ -> Prop} [DecidablePred p] [DecidablePred q] (h : exists n, p n)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `decidablePredExistsNat` / 实例 `decidablePredExistsNat`

English:
instance decidablePredExistsNat
  signature: : DecidablePred fun n' : Nat => exists (n : Nat+) (_ : n' = n), p n
  body: fun n' =>
decidable_of_iff' (exists h : 0 < n', p ⟨n', h⟩)
Subtype.exists.trans by
      simp_rw [mk_coe, @exists_comm (_ < _) (_ = _), exists_prop, exists_eq_left']

中文:
实例 decidablePredExists自然数
  签名: : DecidablePred fun n' : 自然数 => 存在 (n : 自然数+) (_ : n' = n), p n
  定义体: fun n' =>
decidable_of_iff' (exists h : 0 < n', p ⟨n', h⟩)
Subtype.exists.trans by
      simp_rw [mk_coe, @exists_comm (_ < _) (_ = _), exists_prop, exists_eq_left']

Depends on / 依赖: Subtype, Subtype.exists.trans, decidable_of_iff, exists_comm, exists_eq_left, exists_prop, mk_coe, simp_rw
-/
instance decidablePredExistsNat : DecidablePred fun n' : Nat => exists (n : Nat+) (_ : n' = n), p n :=
  fun n' =>
decidable_of_iff' (exists h : 0 < n', p ⟨n', h⟩)
Subtype.exists.trans by
      simp_rw [mk_coe, @exists_comm (_ < _) (_ = _), exists_prop, exists_eq_left']

/--
Definition of `findX` / `findX` 的定义

English:
definition findX
  signature: : { n // p n ∧ forall m : Nat+, m < n -> ¬p m }
  body: by
  have : exists (n' : Nat) (n : Nat+) (_ : n' = n), p n := Exists.elim h fun n hn => ⟨n, n, rfl, hn⟩
  have n := Nat.findX this
  refine ⟨⟨n, ?_⟩, ?_, fun m hm pm => ?_⟩
  · obtain ⟨n', hn', -⟩ := n.prop.1
    rw [hn']
    exact n'.prop
  · obtain ⟨n', hn', pn'⟩ := n.prop.1
    simpa [hn', Subtype.coe_eta] using! pn'
  · exact n.prop.2 m hm ⟨m, rfl, pm⟩

中文:
定义 findX
  签名: : { n // p n ∧ 对任意 m : 自然数+, m < n -> ¬p m }
  定义体: by
  have : exists (n' : Nat) (n : Nat+) (_ : n' = n), p n := Exists.elim h fun n hn => ⟨n, n, rfl, hn⟩
  have n := Nat.findX this
  refine ⟨⟨n, ?_⟩, ?_, fun m hm pm => ?_⟩
  · obtain ⟨n', hn', -⟩ := n.prop.1
    rw [hn']
    exact n'.prop
  · obtain ⟨n', hn', pn'⟩ := n.prop.1
    simpa [hn', Subtype.coe_eta] using! pn'
  · exact n.prop.2 m hm ⟨m, rfl, pm⟩
-/
protected def findX : { n // p n ∧ forall m : Nat+, m < n -> ¬p m } := by
  have : exists (n' : Nat) (n : Nat+) (_ : n' = n), p n := Exists.elim h fun n hn => ⟨n, n, rfl, hn⟩
  have n := Nat.findX this
  refine ⟨⟨n, ?_⟩, ?_, fun m hm pm => ?_⟩
  · obtain ⟨n', hn', -⟩ := n.prop.1
    rw [hn']
    exact n'.prop
  · obtain ⟨n', hn', pn'⟩ := n.prop.1
    simpa [hn', Subtype.coe_eta] using! pn'
  · exact n.prop.2 m hm ⟨m, rfl, pm⟩

/--
Definition of `find` / `find` 的定义

English:
definition find
  signature: : Nat+
  body: PNat.findX h

中文:
定义 find
  签名: : 自然数+
  定义体: PNat.findX h
-/
protected def find : Nat+ :=
  PNat.findX h

/--
theorem `find_spec` / 定理 `find_spec`

English:
theorem find_spec
  statement: p (PNat.find h)
  proof: (PNat.findX h).prop.left

中文:
定理 find_spec
  结论: p (正自然数.find h)
  证明: (PNat.findX h).prop.left
-/
protected theorem find_spec : p (PNat.find h) :=
  (PNat.findX h).prop.left

/--
theorem `find_min` / 定理 `find_min`

English:
theorem find_min
  statement: forall {m : Nat+}, m < PNat.find h -> ¬p m
  proof: @(PNat.findX h).prop.right

中文:
定理 find_min
  结论: 对任意 {m : 自然数+}, m < 正自然数.find h -> ¬p m
  证明: @(PNat.findX h).prop.right
-/
protected theorem find_min : forall {m : Nat+}, m < PNat.find h -> ¬p m :=
  @(PNat.findX h).prop.right

/--
theorem `find_min'` / 定理 `find_min'`

English:
theorem find_min'
  given: {m : Nat+} (hm : p m)
  statement: PNat.find h <= m
  proof: le_of_not_gt fun l => PNat.find_min h l hm

中文:
定理 find_min'
  条件: {m : 自然数+} (hm : p m)
  结论: 正自然数.find h <= m
  证明: le_of_not_gt fun l => PNat.find_min h l hm
-/
protected theorem find_min' {m : Nat+} (hm : p m) : PNat.find h <= m :=
  le_of_not_gt fun l => PNat.find_min h l hm

variable {n m : Nat+}

/--
theorem `find_eq_iff` / 定理 `find_eq_iff`

English:
theorem find_eq_iff
  statement: PNat.find h = m ↔ p m ∧ forall n < m, ¬p n
  proof: by
  constructor
  · rintro rfl
    exact ⟨PNat.find_spec h, fun _ => PNat.find_min h⟩
  · rintro ⟨hm, hlt⟩
    exact le_antisymm (PNat.find_min' h hm) (not_lt.1 <| imp_not_comm.1 (hlt _) <| PNat.find_spec h)

@[simp]

中文:
定理 find_eq_iff
  结论: 正自然数.find h = m ↔ p m ∧ 对任意 n < m, ¬p n
  证明: by
  constructor
  · rintro rfl
    exact ⟨PNat.find_spec h, fun _ => PNat.find_min h⟩
  · rintro ⟨hm, hlt⟩
    exact le_antisymm (PNat.find_min' h hm) (not_lt.1 <| imp_not_comm.1 (hlt _) <| PNat.find_spec h)

@[simp]

Depends on / 依赖: PNat.find_min, PNat.find_spec, find_min, find_spec, imp_not_comm, le_antisymm, not_lt
-/
theorem find_eq_iff : PNat.find h = m ↔ p m ∧ forall n < m, ¬p n := by
  constructor
  · rintro rfl
    exact ⟨PNat.find_spec h, fun _ => PNat.find_min h⟩
  · rintro ⟨hm, hlt⟩
    exact le_antisymm (PNat.find_min' h hm) (not_lt.1 <| imp_not_comm.1 (hlt _) <| PNat.find_spec h)

@[simp]
/--
theorem `find_lt_iff` / 定理 `find_lt_iff`

English:
theorem find_lt_iff
  given: (n : Nat+)
  statement: PNat.find h < n ↔ exists m < n, p m
  proof: ⟨fun h2 => ⟨PNat.find h, h2, PNat.find_spec h⟩, fun ⟨_, hmn, hm⟩ =>
    (PNat.find_min' h hm).trans_lt hmn⟩

@[simp]

中文:
定理 find_lt_iff
  条件: (n : 自然数+)
  结论: 正自然数.find h < n ↔ 存在 m < n, p m
  证明: ⟨fun h2 => ⟨PNat.find h, h2, PNat.find_spec h⟩, fun ⟨_, hmn, hm⟩ =>
    (PNat.find_min' h hm).trans_lt hmn⟩

@[simp]

Depends on / 依赖: PNat.find, PNat.find_min, PNat.find_spec, find_min, find_spec, trans_lt
-/
theorem find_lt_iff (n : Nat+) : PNat.find h < n ↔ exists m < n, p m :=
  ⟨fun h2 => ⟨PNat.find h, h2, PNat.find_spec h⟩, fun ⟨_, hmn, hm⟩ =>
    (PNat.find_min' h hm).trans_lt hmn⟩

@[simp]
/--
theorem `find_le_iff` / 定理 `find_le_iff`

English:
theorem find_le_iff
  given: (n : Nat+)
  statement: PNat.find h <= n ↔ exists m <= n, p m
  proof: by
  simp only [← lt_add_one_iff, find_lt_iff]

@[simp]

中文:
定理 find_le_iff
  条件: (n : 自然数+)
  结论: 正自然数.find h <= n ↔ 存在 m <= n, p m
  证明: by
  simp only [← lt_add_one_iff, find_lt_iff]

@[simp]

Depends on / 依赖: find_lt_iff, lt_add_one_iff
-/
theorem find_le_iff (n : Nat+) : PNat.find h <= n ↔ exists m <= n, p m := by
  simp only [← lt_add_one_iff, find_lt_iff]

@[simp]
/--
theorem `le_find_iff` / 定理 `le_find_iff`

English:
theorem le_find_iff
  given: (n : Nat+)
  statement: n <= PNat.find h ↔ forall m < n, ¬p m
  proof: by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]

@[simp]

中文:
定理 le_find_iff
  条件: (n : 自然数+)
  结论: n <= 正自然数.find h ↔ 对任意 m < n, ¬p m
  证明: by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]

@[simp]

Depends on / 依赖: find_lt_iff, not_and, not_exists, not_lt
-/
theorem le_find_iff (n : Nat+) : n <= PNat.find h ↔ forall m < n, ¬p m := by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]

@[simp]
/--
theorem `lt_find_iff` / 定理 `lt_find_iff`

English:
theorem lt_find_iff
  given: (n : Nat+)
  statement: n < PNat.find h ↔ forall m <= n, ¬p m
  proof: by
  simp only [← add_one_le_iff, le_find_iff, add_le_add_iff_right]

@[simp]

中文:
定理 lt_find_iff
  条件: (n : 自然数+)
  结论: n < 正自然数.find h ↔ 对任意 m <= n, ¬p m
  证明: by
  simp only [← add_one_le_iff, le_find_iff, add_le_add_iff_right]

@[simp]

Depends on / 依赖: add_le_add_iff_right, add_one_le_iff, le_find_iff
-/
theorem lt_find_iff (n : Nat+) : n < PNat.find h ↔ forall m <= n, ¬p m := by
  simp only [← add_one_le_iff, le_find_iff, add_le_add_iff_right]

@[simp]
/--
theorem `find_eq_one` / 定理 `find_eq_one`

English:
theorem find_eq_one
  statement: PNat.find h = 1 ↔ p 1
  proof: by simp [find_eq_iff]

中文:
定理 find_eq_one
  结论: 正自然数.find h = 1 ↔ p 1
  证明: by simp [find_eq_iff]

Depends on / 依赖: find_eq_iff
-/
theorem find_eq_one : PNat.find h = 1 ↔ p 1 := by simp [find_eq_iff]

/--
theorem `one_le_find` / 定理 `one_le_find`

English:
theorem one_le_find
  statement: 1 < PNat.find h ↔ ¬p 1
  proof: by simp

中文:
定理 one_le_find
  结论: 1 < 正自然数.find h ↔ ¬p 1
  证明: by simp
-/
theorem one_le_find : 1 < PNat.find h ↔ ¬p 1 := by simp

/--
theorem `find_mono` / 定理 `find_mono`

English:
theorem find_mono
  given: (h : forall n, q n -> p n) {hp : exists n, p n} {hq : exists n, q n}
  proof: PNat.find_min' _ (h _ (PNat.find_spec hq))

中文:
定理 find_mono
  条件: (h : 对任意 n, q n -> p n) {hp : 存在 n, p n} {hq : 存在 n, q n}
  证明: PNat.find_min' _ (h _ (PNat.find_spec hq))

Depends on / 依赖: PNat.find_min, PNat.find_spec, find_min, find_spec
-/
theorem find_mono (h : forall n, q n -> p n) {hp : exists n, p n} {hq : exists n, q n} :
    PNat.find hp <= PNat.find hq :=
  PNat.find_min' _ (h _ (PNat.find_spec hq))

/--
theorem `find_le` / 定理 `find_le`

English:
theorem find_le
  given: {h : exists n, p n} (hn : p n)
  statement: PNat.find h <= n
  proof: (PNat.find_le_iff _ _).2 ⟨n, le_rfl, hn⟩

中文:
定理 find_le
  条件: {h : 存在 n, p n} (hn : p n)
  结论: 正自然数.find h <= n
  证明: (PNat.find_le_iff _ _).2 ⟨n, le_rfl, hn⟩

Depends on / 依赖: PNat.find_le_iff, find_le_iff, le_rfl
-/
theorem find_le {h : exists n, p n} (hn : p n) : PNat.find h <= n :=
  (PNat.find_le_iff _ _).2 ⟨n, le_rfl, hn⟩

/--
theorem `find_comp_succ` / 定理 `find_comp_succ`

English:
theorem find_comp_succ
  given: (h : exists n, p n) (h₂ : exists n, p (n + 1)) (h1 : ¬p 1)
  proof: by
  refine (find_eq_iff _).2 ⟨PNat.find_spec h₂, fun n => ?_⟩
  induction n with
  | one => simp [h1]
  | succ m _ =>
    intro hm
    simp only [add_lt_add_iff_right, lt_find_iff] at hm
    exact hm _ le_rfl

中文:
定理 find_comp_succ
  条件: (h : 存在 n, p n) (h₂ : 存在 n, p (n + 1)) (h1 : ¬p 1)
  证明: by
  refine (find_eq_iff _).2 ⟨PNat.find_spec h₂, fun n => ?_⟩
  induction n with
  | one => simp [h1]
  | succ m _ =>
    intro hm
    simp only [add_lt_add_iff_right, lt_find_iff] at hm
    exact hm _ le_rfl

Depends on / 依赖: PNat.find_spec, add_lt_add_iff_right, find_eq_iff, find_spec, le_rfl, lt_find_iff
-/
theorem find_comp_succ (h : exists n, p n) (h₂ : exists n, p (n + 1)) (h1 : ¬p 1) :
    PNat.find h = PNat.find h₂ + 1 := by
  refine (find_eq_iff _).2 ⟨PNat.find_spec h₂, fun n => ?_⟩
  induction n with
  | one => simp [h1]
  | succ m _ =>
    intro hm
    simp only [add_lt_add_iff_right, lt_find_iff] at hm
    exact hm _ le_rfl

end PNat
