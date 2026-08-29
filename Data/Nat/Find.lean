/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Push
public import Batteries.Tactic.Init

/-!
# `Nat.find` and `Nat.findGreatest`
-/

@[expose] public section

variable {m n k : Nat} {p q : Nat -> Prop}

namespace Nat

section Find

/-! ### `Nat.find` -/

set_option backward.privateInPublic true in
/--
Definition of `lbp` / `lbp` 的定义

English:
definition lbp
  signature: (m n : Nat)
  body: m = n + 1 ∧ forall k <= n, ¬p k

中文:
定义 lbp
  签名: (m n : 自然数)
  定义体: m = n + 1 ∧ forall k <= n, ¬p k
-/
private def lbp (m n : Nat) : Prop :=
  m = n + 1 ∧ forall k <= n, ¬p k

variable [DecidablePred p] (H : exists n, p n)

set_option linter.defProp false in
set_option backward.privateInPublic true in
/--
Definition of `wf_lbp` / `wf_lbp` 的定义

English:
definition wf_lbp
  signature: : WellFounded (@lbp p)
  body: ⟨let ⟨n, pn⟩ := H
    suffices forall m k, n <= k + m -> Acc lbp k from fun _ => this _ _ (Nat.le_add_left _ _)
    fun m =>
    Nat.recOn m
      (fun _ kn =>
        ⟨_, fun y r =>
          match y, r with
          | _, ⟨rfl, a⟩ => absurd pn (a _ kn)⟩)
      fun m IH k kn =>
      ⟨_, fun y r =>
        match y, r with
        | _, ⟨rfl, _a⟩ => IH _ (by rw [Nat.add_right_comm]; exact kn)⟩⟩

中文:
定义 wf_lbp
  签名: : 良基 (@lbp p)
  定义体: ⟨let ⟨n, pn⟩ := H
    suffices forall m k, n <= k + m -> Acc lbp k from fun _ => this _ _ (Nat.le_add_left _ _)
    fun m =>
    Nat.recOn m
      (fun _ kn =>
        ⟨_, fun y r =>
          match y, r with
          | _, ⟨rfl, a⟩ => absurd pn (a _ kn)⟩)
      fun m IH k kn =>
      ⟨_, fun y r =>
        match y, r with
        | _, ⟨rfl, _a⟩ => IH _ (by rw [Nat.add_right_comm]; exact kn)⟩⟩
-/
private def wf_lbp : WellFounded (@lbp p) :=
  ⟨let ⟨n, pn⟩ := H
    suffices forall m k, n <= k + m -> Acc lbp k from fun _ => this _ _ (Nat.le_add_left _ _)
    fun m =>
    Nat.recOn m
      (fun _ kn =>
        ⟨_, fun y r =>
          match y, r with
          | _, ⟨rfl, a⟩ => absurd pn (a _ kn)⟩)
      fun m IH k kn =>
      ⟨_, fun y r =>
        match y, r with
        | _, ⟨rfl, _a⟩ => IH _ (by rw [Nat.add_right_comm]; exact kn)⟩⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `findX` / `findX` 的定义

English:
definition findX
  signature: : { n // p n ∧ forall m < n, ¬p m }
  body: @WellFounded.fix _ (fun k => (forall n < k, ¬p n) -> { n // p n ∧ forall m < n, ¬p m }) lbp (wf_lbp H)
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : forall n <= m, ¬p n := fun n h =>
          Or.elim (Nat.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
IH _ ⟨rfl, this⟩ fun n h => this n Nat.le_of_succ_le_succ h)
    0 fun _ h => absurd h (Nat.not_lt_zero _)

中文:
定义 findX
  签名: : { n // p n ∧ 对任意 m < n, ¬p m }
  定义体: @WellFounded.fix _ (fun k => (forall n < k, ¬p n) -> { n // p n ∧ forall m < n, ¬p m }) lbp (wf_lbp H)
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : forall n <= m, ¬p n := fun n h =>
          Or.elim (Nat.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
IH _ ⟨rfl, this⟩ fun n h => this n Nat.le_of_succ_le_succ h)
    0 fun _ h => absurd h (Nat.not_lt_zero _)
-/
protected def findX : { n // p n ∧ forall m < n, ¬p m } :=
  @WellFounded.fix _ (fun k => (forall n < k, ¬p n) -> { n // p n ∧ forall m < n, ¬p m }) lbp (wf_lbp H)
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : forall n <= m, ¬p n := fun n h =>
          Or.elim (Nat.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
IH _ ⟨rfl, this⟩ fun n h => this n Nat.le_of_succ_le_succ h)
    0 fun _ h => absurd h (Nat.not_lt_zero _)

/--
Definition of `find` / `find` 的定义

English:
definition find
  signature: : Nat
  body: (Nat.findX H).1

中文:
定义 find
  签名: : 自然数
  定义体: (Nat.findX H).1

Depends on / 依赖: IsSepClosed, PerfectField, isAlgClosed_of_perfectField
-/
protected def find : Nat :=
  (Nat.findX H).1

/--
theorem `find_spec` / 定理 `find_spec`

English:
theorem find_spec
  statement: p (Nat.find H)
  proof: (Nat.findX H).2.left

grind_pattern Nat.find_spec => Nat.find H

中文:
定理 find_spec
  结论: p (自然数.find H)
  证明: (Nat.findX H).2.left

grind_pattern Nat.find_spec => Nat.find H
-/
protected theorem find_spec : p (Nat.find H) :=
  (Nat.findX H).2.left

grind_pattern Nat.find_spec => Nat.find H

/--
theorem `find_min` / 定理 `find_min`

English:
theorem find_min
  statement: forall {m : Nat}, m < Nat.find H -> ¬p m
  proof: @(Nat.findX H).2.right

中文:
定理 find_min
  结论: 对任意 {m : 自然数}, m < 自然数.find H -> ¬p m
  证明: @(Nat.findX H).2.right
-/
protected theorem find_min : forall {m : Nat}, m < Nat.find H -> ¬p m :=
  @(Nat.findX H).2.right

/--
theorem `find_min'` / 定理 `find_min'`

English:
theorem find_min'
  given: {m : Nat} (h : p m)
  statement: Nat.find H <= m
  proof: Nat.le_of_not_gt fun l => Nat.find_min H l h

中文:
定理 find_min'
  条件: {m : 自然数} (h : p m)
  结论: 自然数.find H <= m
  证明: Nat.le_of_not_gt fun l => Nat.find_min H l h
-/
protected theorem find_min' {m : Nat} (h : p m) : Nat.find H <= m :=
  Nat.le_of_not_gt fun l => Nat.find_min H l h

/--
lemma `find_eq_iff` / 引理 `find_eq_iff`

English:
lemma find_eq_iff
  given: (h : exists n : Nat, p n)
  statement: Nat.find h = m ↔ p m ∧ forall n < m, ¬p n
  proof: by
  constructor
  · grind [Nat.find_min]
  · rintro ⟨hm, hlt⟩
    have := Nat.find_min' h hm
    grind

中文:
引理 find_eq_iff
  条件: (h : 存在 n : 自然数, p n)
  结论: 自然数.find h = m ↔ p m ∧ 对任意 n < m, ¬p n
  证明: by
  constructor
  · grind [Nat.find_min]
  · rintro ⟨hm, hlt⟩
    have := Nat.find_min' h hm
    grind

Depends on / 依赖: Nat.find_min, find_min
-/
lemma find_eq_iff (h : exists n : Nat, p n) : Nat.find h = m ↔ p m ∧ forall n < m, ¬p n := by
  constructor
  · grind [Nat.find_min]
  · rintro ⟨hm, hlt⟩
    have := Nat.find_min' h hm
    grind

/--
lemma `find_lt_iff` / 引理 `find_lt_iff`

English:
lemma find_lt_iff
  given: (h : exists n : Nat, p n) (n : Nat)
  statement: Nat.find h < n ↔ exists m < n, p m
  proof: ⟨fun h2 => ⟨Nat.find h, h2, Nat.find_spec h⟩,
    fun ⟨_, hmn, hm⟩ => Nat.lt_of_le_of_lt (Nat.find_min' h hm) hmn⟩

中文:
引理 find_lt_iff
  条件: (h : 存在 n : 自然数, p n) (n : 自然数)
  结论: 自然数.find h < n ↔ 存在 m < n, p m
  证明: ⟨fun h2 => ⟨Nat.find h, h2, Nat.find_spec h⟩,
    fun ⟨_, hmn, hm⟩ => Nat.lt_of_le_of_lt (Nat.find_min' h hm) hmn⟩
-/
@[simp] lemma find_lt_iff (h : exists n : Nat, p n) (n : Nat) : Nat.find h < n ↔ exists m < n, p m :=
  ⟨fun h2 => ⟨Nat.find h, h2, Nat.find_spec h⟩,
    fun ⟨_, hmn, hm⟩ => Nat.lt_of_le_of_lt (Nat.find_min' h hm) hmn⟩

/--
lemma `find_le_iff` / 引理 `find_le_iff`

English:
lemma find_le_iff
  given: (h : exists n : Nat, p n) (n : Nat)
  statement: Nat.find h <= n ↔ exists m <= n, p m
  proof: by
  simp only [← Nat.lt_succ_iff, find_lt_iff]

中文:
引理 find_le_iff
  条件: (h : 存在 n : 自然数, p n) (n : 自然数)
  结论: 自然数.find h <= n ↔ 存在 m <= n, p m
  证明: by
  simp only [← Nat.lt_succ_iff, find_lt_iff]
-/
@[simp] lemma find_le_iff (h : exists n : Nat, p n) (n : Nat) : Nat.find h <= n ↔ exists m <= n, p m := by
  simp only [← Nat.lt_succ_iff, find_lt_iff]

/--
lemma `le_find_iff` / 引理 `le_find_iff`

English:
lemma le_find_iff
  given: (h : exists n : Nat, p n) (n : Nat)
  statement: n <= Nat.find h ↔ forall m < n, ¬p m
  proof: by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]

中文:
引理 le_find_iff
  条件: (h : 存在 n : 自然数, p n) (n : 自然数)
  结论: n <= 自然数.find h ↔ 对任意 m < n, ¬p m
  证明: by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]
-/
@[simp] lemma le_find_iff (h : exists n : Nat, p n) (n : Nat) : n <= Nat.find h ↔ forall m < n, ¬p m := by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]

/--
lemma `lt_find_iff` / 引理 `lt_find_iff`

English:
lemma lt_find_iff
  given: (h : exists n : Nat, p n) (n : Nat)
  statement: n < Nat.find h ↔ forall m <= n, ¬p m
  proof: by
  simp only [← succ_le_iff, le_find_iff, succ_le_succ_iff]

中文:
引理 lt_find_iff
  条件: (h : 存在 n : 自然数, p n) (n : 自然数)
  结论: n < 自然数.find h ↔ 对任意 m <= n, ¬p m
  证明: by
  simp only [← succ_le_iff, le_find_iff, succ_le_succ_iff]
-/
@[simp] lemma lt_find_iff (h : exists n : Nat, p n) (n : Nat) : n < Nat.find h ↔ forall m <= n, ¬p m := by
  simp only [← succ_le_iff, le_find_iff, succ_le_succ_iff]

/--
lemma `find_eq_zero` / 引理 `find_eq_zero`

English:
lemma find_eq_zero
  given: (h : exists n : Nat, p n)
  statement: Nat.find h = 0 ↔ p 0
  proof: by simp [find_eq_iff]

中文:
引理 find_eq_zero
  条件: (h : 存在 n : 自然数, p n)
  结论: 自然数.find h = 0 ↔ p 0
  证明: by simp [find_eq_iff]
-/
@[simp] lemma find_eq_zero (h : exists n : Nat, p n) : Nat.find h = 0 ↔ p 0 := by simp [find_eq_iff]

/--
lemma `find_mono_of_le` / 引理 `find_mono_of_le`

English:
lemma find_mono_of_le
  given: [DecidablePred q] {x : Nat} (hx : q x) (hpq : forall n <= x, q n -> p n)
  proof: Nat.find_min' _ (hpq _ (Nat.find_min' _ hx) (Nat.find_spec ⟨x, hx⟩))

中文:
引理 find_mono_of_le
  条件: [DecidablePred q] {x : 自然数} (hx : q x) (hpq : 对任意 n <= x, q n -> p n)
  证明: Nat.find_min' _ (hpq _ (Nat.find_min' _ hx) (Nat.find_spec ⟨x, hx⟩))

Depends on / 依赖: Nat.find_min, Nat.find_spec, find_min, find_spec
-/
lemma find_mono_of_le [DecidablePred q] {x : Nat} (hx : q x) (hpq : forall n <= x, q n -> p n) :
    Nat.find ⟨x, show p x from hpq _ le_rfl hx⟩ <= Nat.find ⟨x, hx⟩ :=
  Nat.find_min' _ (hpq _ (Nat.find_min' _ hx) (Nat.find_spec ⟨x, hx⟩))

/--
lemma `find_mono` / 引理 `find_mono`

English:
lemma find_mono
  given: [DecidablePred q] (h : forall n, q n -> p n) {hp : exists n, p n} {hq : exists n, q n}
  proof: let ⟨_, hq⟩ := hq; find_mono_of_le hq fun _ _ => h _

中文:
引理 find_mono
  条件: [DecidablePred q] (h : 对任意 n, q n -> p n) {hp : 存在 n, p n} {hq : 存在 n, q n}
  证明: let ⟨_, hq⟩ := hq; find_mono_of_le hq fun _ _ => h _

Depends on / 依赖: find_mono_of_le
-/
lemma find_mono [DecidablePred q] (h : forall n, q n -> p n) {hp : exists n, p n} {hq : exists n, q n} :
    Nat.find hp <= Nat.find hq :=
  let ⟨_, hq⟩ := hq; find_mono_of_le hq fun _ _ => h _

/--
lemma `find_congr` / 引理 `find_congr`

English:
lemma find_congr
  given: [DecidablePred q] {x : Nat} (hx : p x) (hpq : forall n <= x, p n ↔ q n)
  proof: Nat.find ⟨x, hx⟩ = Nat.find ⟨x, show q x from hpq _ le_rfl
  le_antisymm (find_mono_of_le (hpq _ le_rfl |>.1 hx) fun _ h => (hpq _ h).mpr)
    (find_mono_of_le hx fun _ h => (hpq _ h).mp)

中文:
引理 find_congr
  条件: [DecidablePred q] {x : 自然数} (hx : p x) (hpq : 对任意 n <= x, p n ↔ q n)
  证明: Nat.find ⟨x, hx⟩ = Nat.find ⟨x, show q x from hpq _ le_rfl
  le_antisymm (find_mono_of_le (hpq _ le_rfl |>.1 hx) fun _ h => (hpq _ h).mpr)
    (find_mono_of_le hx fun _ h => (hpq _ h).mp)

Depends on / 依赖: Nat.find, le_rfl
-/
lemma find_congr [DecidablePred q] {x : Nat} (hx : p x) (hpq : forall n <= x, p n ↔ q n) :
.1 hx⟩ := Nat.find ⟨x, hx⟩ = Nat.find ⟨x, show q x from hpq _ le_rfl
  le_antisymm (find_mono_of_le (hpq _ le_rfl |>.1 hx) fun _ h => (hpq _ h).mpr)
    (find_mono_of_le hx fun _ h => (hpq _ h).mp)

/--
lemma `find_congr'` / 引理 `find_congr'`

English:
lemma find_congr'
  given: [DecidablePred q] {hp : exists n, p n} {hq : exists n, q n} (hpq : forall {n}, p n ↔ q n)
  proof: let ⟨_, hp⟩ := hp; find_congr hp fun _ _ => hpq

中文:
引理 find_congr'
  条件: [DecidablePred q] {hp : 存在 n, p n} {hq : 存在 n, q n} (hpq : 对任意 {n}, p n ↔ q n)
  证明: let ⟨_, hp⟩ := hp; find_congr hp fun _ _ => hpq

Depends on / 依赖: IsSepClosure, IsSepClosure.isAlgClosure_of_perfectField_top, find_congr, isAlgClosure_of_perfectField_top
-/
lemma find_congr' [DecidablePred q] {hp : exists n, p n} {hq : exists n, q n} (hpq : forall {n}, p n ↔ q n) :
    Nat.find hp = Nat.find hq :=
  let ⟨_, hp⟩ := hp; find_congr hp fun _ _ => hpq

/--
lemma `find_le` / 引理 `find_le`

English:
lemma find_le
  given: {h : exists n, p n} (hn : p n)
  statement: Nat.find h <= n
  proof: (Nat.find_le_iff _ _).2 ⟨n, le_refl _, hn⟩

中文:
引理 find_le
  条件: {h : 存在 n, p n} (hn : p n)
  结论: 自然数.find h <= n
  证明: (Nat.find_le_iff _ _).2 ⟨n, le_refl _, hn⟩

Depends on / 依赖: IsSepClosure, IsSepClosure.isAlgClosure_of_perfectField, Nat.find_le_iff, find_le_iff, isAlgClosure_of_perfectField, le_refl
-/
lemma find_le {h : exists n, p n} (hn : p n) : Nat.find h <= n :=
  (Nat.find_le_iff _ _).2 ⟨n, le_refl _, hn⟩

/--
lemma `find_comp_succ` / 引理 `find_comp_succ`

English:
lemma find_comp_succ
  given: (h₁ : exists n, p n) (h₂ : exists n, p (n + 1)) (h0 : ¬p 0)
  proof: by
  refine (find_eq_iff _).2 ⟨Nat.find_spec h₂, fun n hn => ?_⟩
  cases n
  exacts [h0, @Nat.find_min (fun n => p (n + 1)) _ h₂ _ (succ_lt_succ_iff.1 hn)]

中文:
引理 find_comp_succ
  条件: (h₁ : 存在 n, p n) (h₂ : 存在 n, p (n + 1)) (h0 : ¬p 0)
  证明: by
  refine (find_eq_iff _).2 ⟨Nat.find_spec h₂, fun n hn => ?_⟩
  cases n
  exacts [h0, @Nat.find_min (fun n => p (n + 1)) _ h₂ _ (succ_lt_succ_iff.1 hn)]

Depends on / 依赖: IsSepClosure, IsSepClosure.of_isAlgClosure_of_perfectField, Nat.find_min, Nat.find_spec, exacts, find_eq_iff, find_min, find_spec, of_isAlgClosure_of_perfectField, succ_lt_succ_iff
-/
lemma find_comp_succ (h₁ : exists n, p n) (h₂ : exists n, p (n + 1)) (h0 : ¬p 0) :
    Nat.find h₁ = Nat.find h₂ + 1 := by
  refine (find_eq_iff _).2 ⟨Nat.find_spec h₂, fun n hn => ?_⟩
  cases n
  exacts [h0, @Nat.find_min (fun n => p (n + 1)) _ h₂ _ (succ_lt_succ_iff.1 hn)]

/--
lemma `find_pos` / 引理 `find_pos`

English:
lemma find_pos
  given: (h : exists n : Nat, p n)
  statement: 0 < Nat.find h ↔ ¬p 0
  proof: Nat.pos_iff_ne_zero.trans (Nat.find_eq_zero _).not

中文:
引理 find_pos
  条件: (h : 存在 n : 自然数, p n)
  结论: 0 < 自然数.find h ↔ ¬p 0
  证明: Nat.pos_iff_ne_zero.trans (Nat.find_eq_zero _).not

Depends on / 依赖: Nat.find_eq_zero, Nat.pos_iff_ne_zero.trans, find_eq_zero, pos_iff_ne_zero
-/
lemma find_pos (h : exists n : Nat, p n) : 0 < Nat.find h ↔ ¬p 0 :=
  Nat.pos_iff_ne_zero.trans (Nat.find_eq_zero _).not

/--
lemma `find_add` / 引理 `find_add`

English:
lemma find_add
  given: {hₘ : exists m, p (m + n)} {hₙ : exists n, p n} (hn : n <= Nat.find hₙ)
  proof: by
  refine le_antisymm ((le_find_iff _ _).2 fun m hm hpm => Nat.not_le.2 hm ?_) ?_
  · have hnm : n <= m := le_trans hn (find_le hpm)
    refine Nat.add_le_of_le_sub hnm (find_le ?_)
    rwa [Nat.sub_add_cancel hnm]
  · rw [← Nat.sub_le_iff_le_add]
    refine (le_find_iff _ _).2 fun m hm hpm => Nat.not_le.2 hm ?_
    rw [Nat.sub_le_iff_le_add]
    exact find_le hpm

中文:
引理 find_add
  条件: {hₘ : 存在 m, p (m + n)} {hₙ : 存在 n, p n} (hn : n <= 自然数.find hₙ)
  证明: by
  refine le_antisymm ((le_find_iff _ _).2 fun m hm hpm => Nat.not_le.2 hm ?_) ?_
  · have hnm : n <= m := le_trans hn (find_le hpm)
    refine Nat.add_le_of_le_sub hnm (find_le ?_)
    rwa [Nat.sub_add_cancel hnm]
  · rw [← Nat.sub_le_iff_le_add]
    refine (le_find_iff _ _).2 fun m hm hpm => Nat.not_le.2 hm ?_
    rw [Nat.sub_le_iff_le_add]
    exact find_le hpm

Depends on / 依赖: Nat.add_le_of_le_sub, Nat.not_le, Nat.sub_add_cancel, Nat.sub_le_iff_le_add, add_le_of_le_sub, find_le, le_antisymm, le_find_iff, le_trans, not_le, sub_add_cancel, sub_le_iff_le_add
-/
lemma find_add {hₘ : exists m, p (m + n)} {hₙ : exists n, p n} (hn : n <= Nat.find hₙ) :
    Nat.find hₘ + n = Nat.find hₙ := by
  refine le_antisymm ((le_find_iff _ _).2 fun m hm hpm => Nat.not_le.2 hm ?_) ?_
  · have hnm : n <= m := le_trans hn (find_le hpm)
    refine Nat.add_le_of_le_sub hnm (find_le ?_)
    rwa [Nat.sub_add_cancel hnm]
  · rw [← Nat.sub_le_iff_le_add]
    refine (le_find_iff _ _).2 fun m hm hpm => Nat.not_le.2 hm ?_
    rw [Nat.sub_le_iff_le_add]
    exact find_le hpm

end Find

/-! ### `Nat.findGreatest` -/

section FindGreatest

/--
Definition of `findGreatest` / `findGreatest` 的定义

English:
definition findGreatest
  signature: (P : Nat -> Prop) [DecidablePred P]

中文:
定义 findGreatest
  签名: (P : 自然数 -> 命题) [DecidablePred P]

Depends on / 依赖: Algebra, IsGalois, IsSepClosure, isGalois
-/
def findGreatest (P : Nat -> Prop) [DecidablePred P] : Nat -> Nat
  | 0 => 0
  | n + 1 => if P (n + 1) then n + 1 else Nat.findGreatest P n

variable {P Q : Nat -> Prop} [DecidablePred P] {n : Nat}

/--
lemma `findGreatest_zero` / 引理 `findGreatest_zero`

English:
lemma findGreatest_zero
  statement: Nat.findGreatest P 0 = 0
  proof: (rfl)

中文:
引理 findGreatest_zero
  结论: 自然数.findGreatest P 0 = 0
  证明: (rfl)
-/
@[simp] lemma findGreatest_zero : Nat.findGreatest P 0 = 0 := (rfl)

/--
lemma `findGreatest_succ` / 引理 `findGreatest_succ`

English:
lemma findGreatest_succ
  given: (n : Nat)
  proof: (rfl)

中文:
引理 findGreatest_succ
  条件: (n : 自然数)
  证明: (rfl)
-/
lemma findGreatest_succ (n : Nat) :
    Nat.findGreatest P (n + 1) = if P (n + 1) then n + 1 else Nat.findGreatest P n := (rfl)

/--
lemma `findGreatest_eq` / 引理 `findGreatest_eq`

English:
lemma findGreatest_eq
  statement: forall {n}, P n -> Nat.findGreatest P n = n

中文:
引理 findGreatest_eq
  结论: 对任意 {n}, P n -> 自然数.findGreatest P n = n
-/
@[simp] lemma findGreatest_eq : forall {n}, P n -> Nat.findGreatest P n = n
  | 0, _ => rfl
  | n + 1, h => by simp [Nat.findGreatest, h]

@[simp]
/--
lemma `findGreatest_of_not` / 引理 `findGreatest_of_not`

English:
lemma findGreatest_of_not
  given: (h : ¬ P (n + 1))
  statement: findGreatest P (n + 1) = findGreatest P n
  proof: by
  simp [Nat.findGreatest, h]

中文:
引理 findGreatest_of_not
  条件: (h : ¬ P (n + 1))
  结论: findGreatest P (n + 1) = findGreatest P n
  证明: by
  simp [Nat.findGreatest, h]

Depends on / 依赖: Nat.findGreatest, findGreatest
-/
lemma findGreatest_of_not (h : ¬ P (n + 1)) : findGreatest P (n + 1) = findGreatest P n := by
  simp [Nat.findGreatest, h]

/--
lemma `findGreatest_eq_iff` / 引理 `findGreatest_eq_iff`

English:
lemma findGreatest_eq_iff
  proof: by
  induction k generalizing m with
  | zero =>
    rw [eq_comm]; rw [Iff.comm]
    simp only [Nat.le_zero, ne_eq, findGreatest_zero, and_iff_left_iff_imp]
    rintro rfl
    exact ⟨fun h => (h rfl).elim, fun n hlt heq => by lia⟩
  | succ k ihk =>
    by_cases hk : P (k + 1)
    · rw [findGreatest_eq hk]
      constructor
      · rintro rfl
        exact ⟨le_refl _, fun _ => hk, fun n hlt hle => by lia⟩
      · rintro ⟨hle, h0, hm⟩
        rcases Decidable.lt_or_eq_of_le hle with hlt | rfl
        exacts [(hm hlt (le_refl _) hk).elim, rfl]
    · rw [findGreatest_of_not hk, ihk]
      grind

中文:
引理 findGreatest_eq_iff
  证明: by
  induction k generalizing m with
  | zero =>
    rw [eq_comm]; rw [Iff.comm]
    simp only [Nat.le_zero, ne_eq, findGreatest_zero, and_iff_left_iff_imp]
    rintro rfl
    exact ⟨fun h => (h rfl).elim, fun n hlt heq => by lia⟩
  | succ k ihk =>
    by_cases hk : P (k + 1)
    · rw [findGreatest_eq hk]
      constructor
      · rintro rfl
        exact ⟨le_refl _, fun _ => hk, fun n hlt hle => by lia⟩
      · rintro ⟨hle, h0, hm⟩
        rcases Decidable.lt_or_eq_of_le hle with hlt | rfl
        exacts [(hm hlt (le_refl _) hk).elim, rfl]
    · rw [findGreatest_of_not hk, ihk]
      grind

Depends on / 依赖: Decidable, Decidable.lt_or_eq_of_le, Iff.comm, Nat.le_zero, and_iff_left_iff_imp, eq_comm, exacts, findGreatest_eq, findGreatest_of_not, findGreatest_zero, generalizing, le_refl, le_zero, lt_or_eq_of_le, ne_eq
-/
lemma findGreatest_eq_iff :
    Nat.findGreatest P k = m ↔ m <= k ∧ (m != 0 -> P m) ∧ forall ⦃n⦄, m < n -> n <= k -> ¬P n := by
  induction k generalizing m with
  | zero =>
    rw [eq_comm]; rw [Iff.comm]
    simp only [Nat.le_zero, ne_eq, findGreatest_zero, and_iff_left_iff_imp]
    rintro rfl
    exact ⟨fun h => (h rfl).elim, fun n hlt heq => by lia⟩
  | succ k ihk =>
    by_cases hk : P (k + 1)
    · rw [findGreatest_eq hk]
      constructor
      · rintro rfl
        exact ⟨le_refl _, fun _ => hk, fun n hlt hle => by lia⟩
      · rintro ⟨hle, h0, hm⟩
        rcases Decidable.lt_or_eq_of_le hle with hlt | rfl
        exacts [(hm hlt (le_refl _) hk).elim, rfl]
    · rw [findGreatest_of_not hk, ihk]
      grind

/--
lemma `findGreatest_eq_zero_iff` / 引理 `findGreatest_eq_zero_iff`

English:
lemma findGreatest_eq_zero_iff
  statement: Nat.findGreatest P k = 0 ↔ forall ⦃n⦄, 0 < n -> n <= k -> ¬P n
  proof: by
  simp [findGreatest_eq_iff]

中文:
引理 findGreatest_eq_zero_iff
  结论: 自然数.findGreatest P k = 0 ↔ 对任意 ⦃n⦄, 0 < n -> n <= k -> ¬P n
  证明: by
  simp [findGreatest_eq_iff]

Depends on / 依赖: findGreatest_eq_iff
-/
lemma findGreatest_eq_zero_iff : Nat.findGreatest P k = 0 ↔ forall ⦃n⦄, 0 < n -> n <= k -> ¬P n := by
  simp [findGreatest_eq_iff]

/--
lemma `findGreatest_pos` / 引理 `findGreatest_pos`

English:
lemma findGreatest_pos
  statement: 0 < Nat.findGreatest P k ↔ exists n, 0 < n ∧ n <= k ∧ P n
  proof: by
  rw [Nat.pos_iff_ne_zero]; rw [Ne]; rw [findGreatest_eq_zero_iff]; push Not; rfl

中文:
引理 findGreatest_pos
  结论: 0 < 自然数.findGreatest P k ↔ 存在 n, 0 < n ∧ n <= k ∧ P n
  证明: by
  rw [Nat.pos_iff_ne_zero]; rw [Ne]; rw [findGreatest_eq_zero_iff]; push Not; rfl
-/
@[simp] lemma findGreatest_pos : 0 < Nat.findGreatest P k ↔ exists n, 0 < n ∧ n <= k ∧ P n := by
  rw [Nat.pos_iff_ne_zero]; rw [Ne]; rw [findGreatest_eq_zero_iff]; push Not; rfl

/--
lemma `findGreatest_spec` / 引理 `findGreatest_spec`

English:
lemma findGreatest_spec
  given: (hmb : m <= n) (hm : P m)
  statement: P (Nat.findGreatest P n)
  proof: by
  by_cases h : Nat.findGreatest P n = 0
  · cases m
    · rwa [h]
    exact ((findGreatest_eq_zero_iff.1 h) (zero_lt_succ _) hmb hm).elim
  · exact (findGreatest_eq_iff.1 rfl).2.1 h

中文:
引理 findGreatest_spec
  条件: (hmb : m <= n) (hm : P m)
  结论: P (自然数.findGreatest P n)
  证明: by
  by_cases h : Nat.findGreatest P n = 0
  · cases m
    · rwa [h]
    exact ((findGreatest_eq_zero_iff.1 h) (zero_lt_succ _) hmb hm).elim
  · exact (findGreatest_eq_iff.1 rfl).2.1 h

Depends on / 依赖: Nat.findGreatest, findGreatest, findGreatest_eq_iff, findGreatest_eq_zero_iff, zero_lt_succ
-/
lemma findGreatest_spec (hmb : m <= n) (hm : P m) : P (Nat.findGreatest P n) := by
  by_cases h : Nat.findGreatest P n = 0
  · cases m
    · rwa [h]
    exact ((findGreatest_eq_zero_iff.1 h) (zero_lt_succ _) hmb hm).elim
  · exact (findGreatest_eq_iff.1 rfl).2.1 h

/--
lemma `findGreatest_le` / 引理 `findGreatest_le`

English:
lemma findGreatest_le
  given: (n : Nat)
  statement: Nat.findGreatest P n <= n
  proof: (findGreatest_eq_iff.1 rfl).1

中文:
引理 findGreatest_le
  条件: (n : 自然数)
  结论: 自然数.findGreatest P n <= n
  证明: (findGreatest_eq_iff.1 rfl).1

Depends on / 依赖: findGreatest_eq_iff
-/
lemma findGreatest_le (n : Nat) : Nat.findGreatest P n <= n :=
  (findGreatest_eq_iff.1 rfl).1

/--
lemma `le_findGreatest` / 引理 `le_findGreatest`

English:
lemma le_findGreatest
  given: (hmb : m <= n) (hm : P m)
  statement: m <= Nat.findGreatest P n
  proof: le_of_not_gt fun hlt => (findGreatest_eq_iff.1 rfl).2.2 hlt hmb hm

中文:
引理 le_findGreatest
  条件: (hmb : m <= n) (hm : P m)
  结论: m <= 自然数.findGreatest P n
  证明: le_of_not_gt fun hlt => (findGreatest_eq_iff.1 rfl).2.2 hlt hmb hm

Depends on / 依赖: findGreatest_eq_iff, le_of_not_gt
-/
lemma le_findGreatest (hmb : m <= n) (hm : P m) : m <= Nat.findGreatest P n :=
  le_of_not_gt fun hlt => (findGreatest_eq_iff.1 rfl).2.2 hlt hmb hm

/--
lemma `findGreatest_mono_right` / 引理 `findGreatest_mono_right`

English:
lemma findGreatest_mono_right
  given: (P : Nat -> Prop) [DecidablePred P] {m n} (hmn : m <= n)
  proof: by
  induction hmn with
  | refl => simp
  | step hmk ih =>
    rw [findGreatest_succ]
    split_ifs
· exact le_trans ih le_trans (findGreatest_le _) (le_succ _)
    · exact ih

中文:
引理 findGreatest_mono_right
  条件: (P : 自然数 -> 命题) [DecidablePred P] {m n} (hmn : m <= n)
  证明: by
  induction hmn with
  | refl => simp
  | step hmk ih =>
    rw [findGreatest_succ]
    split_ifs
· exact le_trans ih le_trans (findGreatest_le _) (le_succ _)
    · exact ih

Depends on / 依赖: findGreatest_le, findGreatest_succ, le_succ, le_trans, split_ifs
-/
lemma findGreatest_mono_right (P : Nat -> Prop) [DecidablePred P] {m n} (hmn : m <= n) :
    Nat.findGreatest P m <= Nat.findGreatest P n := by
  induction hmn with
  | refl => simp
  | step hmk ih =>
    rw [findGreatest_succ]
    split_ifs
· exact le_trans ih le_trans (findGreatest_le _) (le_succ _)
    · exact ih

/--
lemma `findGreatest_mono_left` / 引理 `findGreatest_mono_left`

English:
lemma findGreatest_mono_left
  given: [DecidablePred Q] (hPQ : forall n, P n -> Q n) (n : Nat)
  proof: by
  induction n with
  | zero => rfl
  | succ n hn =>
    by_cases h : P (n + 1)
    · rw [findGreatest_eq h, findGreatest_eq (hPQ _ h)]
    · rw [findGreatest_of_not h]
      exact le_trans hn (Nat.findGreatest_mono_right _ <| le_succ _)

中文:
引理 findGreatest_mono_left
  条件: [DecidablePred Q] (hPQ : 对任意 n, P n -> Q n) (n : 自然数)
  证明: by
  induction n with
  | zero => rfl
  | succ n hn =>
    by_cases h : P (n + 1)
    · rw [findGreatest_eq h, findGreatest_eq (hPQ _ h)]
    · rw [findGreatest_of_not h]
      exact le_trans hn (Nat.findGreatest_mono_right _ <| le_succ _)

Depends on / 依赖: Nat.findGreatest_mono_right, findGreatest_eq, findGreatest_mono_right, findGreatest_of_not, le_succ, le_trans
-/
lemma findGreatest_mono_left [DecidablePred Q] (hPQ : forall n, P n -> Q n) (n : Nat) :
    Nat.findGreatest P n <= Nat.findGreatest Q n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    by_cases h : P (n + 1)
    · rw [findGreatest_eq h, findGreatest_eq (hPQ _ h)]
    · rw [findGreatest_of_not h]
      exact le_trans hn (Nat.findGreatest_mono_right _ <| le_succ _)

/--
lemma `findGreatest_mono` / 引理 `findGreatest_mono`

English:
lemma findGreatest_mono
  given: [DecidablePred Q] (hPQ : forall n, P n -> Q n) (hmn : m <= n)
  proof: le_trans (Nat.findGreatest_mono_right _ hmn) (findGreatest_mono_left hPQ _)

中文:
引理 findGreatest_mono
  条件: [DecidablePred Q] (hPQ : 对任意 n, P n -> Q n) (hmn : m <= n)
  证明: le_trans (Nat.findGreatest_mono_right _ hmn) (findGreatest_mono_left hPQ _)

Depends on / 依赖: Nat.findGreatest_mono_right, findGreatest_mono_left, findGreatest_mono_right, le_trans
-/
lemma findGreatest_mono [DecidablePred Q] (hPQ : forall n, P n -> Q n) (hmn : m <= n) :
    Nat.findGreatest P m <= Nat.findGreatest Q n :=
  le_trans (Nat.findGreatest_mono_right _ hmn) (findGreatest_mono_left hPQ _)

/--
theorem `findGreatest_is_greatest` / 定理 `findGreatest_is_greatest`

English:
theorem findGreatest_is_greatest
  given: (hk : Nat.findGreatest P n < k) (hkb : k <= n)
  statement: ¬P k
  proof: (findGreatest_eq_iff.1 rfl).2.2 hk hkb

中文:
定理 findGreatest_is_greatest
  条件: (hk : 自然数.findGreatest P n < k) (hkb : k <= n)
  结论: ¬P k
  证明: (findGreatest_eq_iff.1 rfl).2.2 hk hkb

Depends on / 依赖: findGreatest_eq_iff
-/
theorem findGreatest_is_greatest (hk : Nat.findGreatest P n < k) (hkb : k <= n) : ¬P k :=
  (findGreatest_eq_iff.1 rfl).2.2 hk hkb

/--
theorem `findGreatest_of_ne_zero` / 定理 `findGreatest_of_ne_zero`

English:
theorem findGreatest_of_ne_zero
  given: (h : Nat.findGreatest P n = m) (h0 : m != 0)
  statement: P m
  proof: (findGreatest_eq_iff.1 h).2.1 h0

中文:
定理 findGreatest_of_ne_zero
  条件: (h : 自然数.findGreatest P n = m) (h0 : m != 0)
  结论: P m
  证明: (findGreatest_eq_iff.1 h).2.1 h0

Depends on / 依赖: findGreatest_eq_iff
-/
theorem findGreatest_of_ne_zero (h : Nat.findGreatest P n = m) (h0 : m != 0) : P m :=
  (findGreatest_eq_iff.1 h).2.1 h0

end FindGreatest

end Nat
