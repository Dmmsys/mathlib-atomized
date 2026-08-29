/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.Nat.PSub
public import Mathlib.Data.PFun

/-!
# The partial recursive functions

The partial recursive functions are defined similarly to the primitive
recursive functions, but now all functions are partial, implemented
using the `Part` monad, and there is an additional operation, called
μ-recursion, which performs unbounded minimization: `μ f` returns the
least natural number `n` for which `f n = 0`, or diverges if such `n` doesn't exist.

## Main definitions

- `Nat.Partrec f`: `f` is partial recursive, for functions `f : ℕ →. ℕ`
- `Partrec f`: `f` is partial recursive, for partial functions between `Primcodable` types
- `Computable f`: `f` is partial recursive, for total functions between `Primcodable` types

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

@[expose] public section

open List (Vector)
open Encodable Denumerable Part

attribute [-simp] not_forall

namespace Nat

section Rfind

variable (p : Nat ->. Bool)

set_option backward.privateInPublic true in
/--
Definition of `lbp` / `lbp` 的定义

English:
definition lbp
  signature: (m n : Nat)
  body: m = n + 1 ∧ forall k <= n, false in p k

中文:
定义 lbp
  签名: (m n : 自然数)
  定义体: m = n + 1 ∧ forall k <= n, false in p k
-/
private def lbp (m n : Nat) : Prop :=
  m = n + 1 ∧ forall k <= n, false in p k

set_option linter.defProp false in
set_option backward.privateInPublic true in
/--
Definition of `wf_lbp` / `wf_lbp` 的定义

English:
definition wf_lbp
  signature: (H : exists n, true in p n ∧ forall k < n, (p k).Dom)
  body: ⟨by
    let ⟨n, pn⟩ := H
    suffices forall m k, n <= k + m -> Acc (lbp p) k by exact fun a => this _ _ (Nat.le_add_left _ _)
    intro m k kn
    induction m generalizing k with (refine ⟨_, fun y r => ?_⟩; rcases r with ⟨rfl, a⟩)
    | zero => injection mem_unique pn.1 (a _ kn)
    | succ m IH => 

中文:
定义 wf_lbp
  签名: (H : 存在 n, true in p n ∧ 对任意 k < n, (p k).Dom)
  定义体: ⟨by
    let ⟨n, pn⟩ := H
    suffices forall m k, n <= k + m -> Acc (lbp p) k by exact fun a => this _ _ (Nat.le_add_left _ _)
    intro m k kn
    induction m generalizing k with (refine ⟨_, fun y r => ?_⟩; rcases r with ⟨rfl, a⟩)
    | zero => injection mem_unique pn.1 (a _ kn)
    | succ m IH => 
-/
private def wf_lbp (H : exists n, true in p n ∧ forall k < n, (p k).Dom) : WellFounded (lbp p) :=
  ⟨by
    let ⟨n, pn⟩ := H
    suffices forall m k, n <= k + m -> Acc (lbp p) k by exact fun a => this _ _ (Nat.le_add_left _ _)
    intro m k kn
    induction m generalizing k with (refine ⟨_, fun y r => ?_⟩; rcases r with ⟨rfl, a⟩)
    | zero => injection mem_unique pn.1 (a _ kn)
    | succ m IH => exact IH _ (by rw [Nat.add_right_comm]; exact kn)⟩

variable (H : exists n, true in p n ∧ forall k < n, (p k).Dom)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `rfindX` / `rfindX` 的定义

English:
definition rfindX
  signature: : { n // true in p n ∧ forall m < n, false in p m }
  body: suffices forall k, (forall n < k, false in p n) -> { n // true in p n ∧ forall m < n, false in p m } from
    this 0 fun _ => (Nat.not_lt_zero _).elim
  @WellFounded.fix _ _ (lbp p) (wf_lbp p H)
    (by
      intro m IH al
      have pm : (p m).Dom := by
        rcases H with ⟨n, h₁, h₂⟩
        rca

中文:
定义 rfindX
  签名: : { n // true in p n ∧ 对任意 m < n, false in p m }
  定义体: suffices forall k, (forall n < k, false in p n) -> { n // true in p n ∧ forall m < n, false in p m } from
    this 0 fun _ => (Nat.not_lt_zero _).elim
  @WellFounded.fix _ _ (lbp p) (wf_lbp p H)
    (by
      intro m IH al
      have pm : (p m).Dom := by
        rcases H with ⟨n, h₁, h₂⟩
        rca

Depends on / 依赖: Nat.not_lt_zero, WellFounded, WellFounded.fix, injection, le_of_lt_succ, lt_trichotomy, mem_unique, not_lt_zero, wf_lbp
-/
def rfindX : { n // true in p n ∧ forall m < n, false in p m } :=
  suffices forall k, (forall n < k, false in p n) -> { n // true in p n ∧ forall m < n, false in p m } from
    this 0 fun _ => (Nat.not_lt_zero _).elim
  @WellFounded.fix _ _ (lbp p) (wf_lbp p H)
    (by
      intro m IH al
      have pm : (p m).Dom := by
        rcases H with ⟨n, h₁, h₂⟩
        rcases lt_trichotomy m n with (h₃ | h₃ | h₃)
        · exact h₂ _ h₃
        · rw [h₃]
          exact h₁.fst
        · injection mem_unique h₁ (al _ h₃)
      cases e : (p m).get pm
      · suffices forallᵉ k <= m, false in p k from IH _ ⟨rfl, this⟩ fun n h => this _ (le_of_lt_succ h)
        intro n h
        rcases h.lt_or_eq_dec with h | h
        · exact al _ h
        · rw [h]
          exact ⟨_, e⟩
      · exact ⟨m, ⟨_, e⟩, al⟩)

end Rfind

/--
Definition of `rfind` / `rfind` 的定义

English:
definition rfind
  signature: (p : Nat ->. Bool)
  body: ⟨_, fun h => (rfindX p h).1⟩

中文:
定义 rfind
  签名: (p : 自然数 ->. 布尔值)
  定义体: ⟨_, fun h => (rfindX p h).1⟩

Depends on / 依赖: rfindX
-/
def rfind (p : Nat ->. Bool) : Part Nat :=
  ⟨_, fun h => (rfindX p h).1⟩

/--
theorem `rfind_spec` / 定理 `rfind_spec`

English:
theorem rfind_spec
  given: {p : Nat ->. Bool} {n : Nat} (h : n in rfind p)
  statement: true in p n
  proof: h.snd ▸ (rfindX p h.fst).2.1

中文:
定理 rfind_spec
  条件: {p : 自然数 ->. 布尔值} {n : 自然数} (h : n in rfind p)
  结论: true in p n
  证明: h.snd ▸ (rfindX p h.fst).2.1

Depends on / 依赖: h.fst, h.snd, rfindX
-/
theorem rfind_spec {p : Nat ->. Bool} {n : Nat} (h : n in rfind p) : true in p n :=
  h.snd ▸ (rfindX p h.fst).2.1

/--
theorem `rfind_min` / 定理 `rfind_min`

English:
theorem rfind_min
  given: {p : Nat ->. Bool} {n : Nat} (h : n in rfind p)
  statement: forall {m : Nat}, m < n -> false in p m
  proof: @(h.snd ▸ @((rfindX p h.fst).2.2))

@[simp]

中文:
定理 rfind_min
  条件: {p : 自然数 ->. 布尔值} {n : 自然数} (h : n in rfind p)
  结论: 对任意 {m : 自然数}, m < n -> false in p m
  证明: @(h.snd ▸ @((rfindX p h.fst).2.2))

@[simp]

Depends on / 依赖: h.fst, h.snd, rfindX
-/
theorem rfind_min {p : Nat ->. Bool} {n : Nat} (h : n in rfind p) : forall {m : Nat}, m < n -> false in p m :=
  @(h.snd ▸ @((rfindX p h.fst).2.2))

@[simp]
/--
theorem `rfind_dom` / 定理 `rfind_dom`

English:
theorem rfind_dom
  given: {p : Nat ->. Bool}
  proof: Iff.rfl

中文:
定理 rfind_dom
  条件: {p : 自然数 ->. 布尔值}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem rfind_dom {p : Nat ->. Bool} :
    (rfind p).Dom ↔ exists n, true in p n ∧ forall {m : Nat}, m < n -> (p m).Dom :=
  Iff.rfl

/--
theorem `rfind_dom'` / 定理 `rfind_dom'`

English:
theorem rfind_dom'
  given: {p : Nat ->. Bool}
  proof: exists_congr fun _ =>
    and_congr_right fun pn =>
      ⟨fun H _ h => (Decidable.eq_or_lt_of_le h).elim (fun e => e.symm ▸ pn.fst) (H _), fun H _ h =>
        H (le_of_lt h)⟩

@[simp]

中文:
定理 rfind_dom'
  条件: {p : 自然数 ->. 布尔值}
  证明: exists_congr fun _ =>
    and_congr_right fun pn =>
      ⟨fun H _ h => (Decidable.eq_or_lt_of_le h).elim (fun e => e.symm ▸ pn.fst) (H _), fun H _ h =>
        H (le_of_lt h)⟩

@[simp]

Depends on / 依赖: Decidable, Decidable.eq_or_lt_of_le, and_congr_right, e.symm, eq_or_lt_of_le, exists_congr, le_of_lt, pn.fst
-/
theorem rfind_dom' {p : Nat ->. Bool} :
    (rfind p).Dom ↔ exists n, true in p n ∧ forall {m : Nat}, m <= n -> (p m).Dom :=
  exists_congr fun _ =>
    and_congr_right fun pn =>
      ⟨fun H _ h => (Decidable.eq_or_lt_of_le h).elim (fun e => e.symm ▸ pn.fst) (H _), fun H _ h =>
        H (le_of_lt h)⟩

@[simp]
/--
theorem `mem_rfind` / 定理 `mem_rfind`

English:
theorem mem_rfind
  given: {p : Nat ->. Bool} {n : Nat}
  proof: ⟨fun h => ⟨rfind_spec h, @rfind_min _ _ h⟩, fun ⟨h₁, h₂⟩ => by
let ⟨m, hm⟩ := dom_iff_mem.1 (@rfind_dom p).2 ⟨_, h₁, fun {m} mn => (h₂ mn).fst⟩
    rcases lt_trichotomy m n with (h | h | h)
    · injection mem_unique (h₂ h) (rfind_spec hm)
    · rwa [← h]
    · injection mem_unique h₁ (rfind_min hm 

中文:
定理 mem_rfind
  条件: {p : 自然数 ->. 布尔值} {n : 自然数}
  证明: ⟨fun h => ⟨rfind_spec h, @rfind_min _ _ h⟩, fun ⟨h₁, h₂⟩ => by
let ⟨m, hm⟩ := dom_iff_mem.1 (@rfind_dom p).2 ⟨_, h₁, fun {m} mn => (h₂ mn).fst⟩
    rcases lt_trichotomy m n with (h | h | h)
    · injection mem_unique (h₂ h) (rfind_spec hm)
    · rwa [← h]
    · injection mem_unique h₁ (rfind_min hm 

Depends on / 依赖: dom_iff_mem, injection, lt_trichotomy, mem_unique, rfind_dom, rfind_min, rfind_spec
-/
theorem mem_rfind {p : Nat ->. Bool} {n : Nat} :
    n in rfind p ↔ true in p n ∧ forall {m : Nat}, m < n -> false in p m :=
  ⟨fun h => ⟨rfind_spec h, @rfind_min _ _ h⟩, fun ⟨h₁, h₂⟩ => by
let ⟨m, hm⟩ := dom_iff_mem.1 (@rfind_dom p).2 ⟨_, h₁, fun {m} mn => (h₂ mn).fst⟩
    rcases lt_trichotomy m n with (h | h | h)
    · injection mem_unique (h₂ h) (rfind_spec hm)
    · rwa [← h]
    · injection mem_unique h₁ (rfind_min hm h)⟩

/--
theorem `rfind_min'` / 定理 `rfind_min'`

English:
theorem rfind_min'
  given: {p : Nat -> Bool} {m : Nat} (pm : p m)
  statement: exists n in rfind p, n <= m
  proof: have : true in (p : Nat ->. Bool) m := ⟨trivial, pm⟩
let ⟨n, hn⟩ := dom_iff_mem.1 (@rfind_dom p).2 ⟨m, this, fun {_} _ => ⟨⟩⟩
  ⟨n, hn, not_lt.1 fun h => by injection mem_unique this (rfind_min hn h)⟩

中文:
定理 rfind_min'
  条件: {p : 自然数 -> 布尔值} {m : 自然数} (pm : p m)
  结论: 存在 n in rfind p, n <= m
  证明: have : true in (p : Nat ->. Bool) m := ⟨trivial, pm⟩
let ⟨n, hn⟩ := dom_iff_mem.1 (@rfind_dom p).2 ⟨m, this, fun {_} _ => ⟨⟩⟩
  ⟨n, hn, not_lt.1 fun h => by injection mem_unique this (rfind_min hn h)⟩

Depends on / 依赖: dom_iff_mem, injection, mem_unique, not_lt, rfind_dom, rfind_min
-/
theorem rfind_min' {p : Nat -> Bool} {m : Nat} (pm : p m) : exists n in rfind p, n <= m :=
  have : true in (p : Nat ->. Bool) m := ⟨trivial, pm⟩
let ⟨n, hn⟩ := dom_iff_mem.1 (@rfind_dom p).2 ⟨m, this, fun {_} _ => ⟨⟩⟩
  ⟨n, hn, not_lt.1 fun h => by injection mem_unique this (rfind_min hn h)⟩

/--
theorem `rfind_zero_none` / 定理 `rfind_zero_none`

English:
theorem rfind_zero_none
  given: (p : Nat ->. Bool) (p0 : p 0 = Part.none)
  statement: rfind p = Part.none
  proof: eq_none_iff.2 fun _ h =>
    let ⟨_, _, h₂⟩ := rfind_dom'.1 h.fst
    (p0 ▸ h₂ (zero_le _) : (@Part.none Bool).Dom)

中文:
定理 rfind_zero_none
  条件: (p : 自然数 ->. 布尔值) (p0 : p 0 = Part.none)
  结论: rfind p = Part.none
  证明: eq_none_iff.2 fun _ h =>
    let ⟨_, _, h₂⟩ := rfind_dom'.1 h.fst
    (p0 ▸ h₂ (zero_le _) : (@Part.none Bool).Dom)

Depends on / 依赖: Part.none, eq_none_iff, h.fst, rfind_dom, zero_le
-/
theorem rfind_zero_none (p : Nat ->. Bool) (p0 : p 0 = Part.none) : rfind p = Part.none :=
  eq_none_iff.2 fun _ h =>
    let ⟨_, _, h₂⟩ := rfind_dom'.1 h.fst
    (p0 ▸ h₂ (zero_le _) : (@Part.none Bool).Dom)

/--
Definition of `rfindOpt` / `rfindOpt` 的定义

English:
definition rfindOpt
  signature: {α} (f : Nat -> Option α)
  body: (rfind fun n => (f n).isSome).bind fun n => f n

中文:
定义 rfindOpt
  签名: {α} (f : 自然数 -> 选项类型 α)
  定义体: (rfind fun n => (f n).isSome).bind fun n => f n

Depends on / 依赖: isSome
-/
def rfindOpt {α} (f : Nat -> Option α) : Part α :=
  (rfind fun n => (f n).isSome).bind fun n => f n

/--
theorem `rfindOpt_spec` / 定理 `rfindOpt_spec`

English:
theorem rfindOpt_spec
  given: {α} {f : Nat -> Option α} {a} (h : a in rfindOpt f)
  statement: exists n, a in f n
  proof: let ⟨n, _, h₂⟩ := mem_bind_iff.1 h
  ⟨n, mem_coe.1 h₂⟩

中文:
定理 rfindOpt_spec
  条件: {α} {f : 自然数 -> 选项类型 α} {a} (h : a in rfindOpt f)
  结论: 存在 n, a in f n
  证明: let ⟨n, _, h₂⟩ := mem_bind_iff.1 h
  ⟨n, mem_coe.1 h₂⟩

Depends on / 依赖: mem_bind_iff, mem_coe
-/
theorem rfindOpt_spec {α} {f : Nat -> Option α} {a} (h : a in rfindOpt f) : exists n, a in f n :=
  let ⟨n, _, h₂⟩ := mem_bind_iff.1 h
  ⟨n, mem_coe.1 h₂⟩

/--
theorem `rfindOpt_dom` / 定理 `rfindOpt_dom`

English:
theorem rfindOpt_dom
  given: {α} {f : Nat -> Option α}
  statement: (rfindOpt f).Dom ↔ exists n a, a in f n
  proof: ⟨fun h => (rfindOpt_spec ⟨h, rfl⟩).imp fun _ h => ⟨_, h⟩, fun h => by
    have h' : exists n, (f n).isSome := h.imp fun n => Option.isSome_iff_exists.2
    have s := Nat.find_spec h'
    have fd : (rfind fun n => (f n).isSome).Dom :=
      ⟨Nat.find h', by simpa using s.symm, fun _ _ => trivial⟩
   

中文:
定理 rfindOpt_dom
  条件: {α} {f : 自然数 -> 选项类型 α}
  结论: (rfindOpt f).Dom ↔ 存在 n a, a in f n
  证明: ⟨fun h => (rfindOpt_spec ⟨h, rfl⟩).imp fun _ h => ⟨_, h⟩, fun h => by
    have h' : exists n, (f n).isSome := h.imp fun n => Option.isSome_iff_exists.2
    have s := Nat.find_spec h'
    have fd : (rfind fun n => (f n).isSome).Dom :=
      ⟨Nat.find h', by simpa using s.symm, fun _ _ => trivial⟩
   

Depends on / 依赖: Nat.find, Nat.find_spec, Option.isSome_iff_exists, find_spec, get_mem, h.imp, isSome, isSome_iff_exists, rfindOpt_spec, rfind_spec, s.symm
-/
theorem rfindOpt_dom {α} {f : Nat -> Option α} : (rfindOpt f).Dom ↔ exists n a, a in f n :=
  ⟨fun h => (rfindOpt_spec ⟨h, rfl⟩).imp fun _ h => ⟨_, h⟩, fun h => by
    have h' : exists n, (f n).isSome := h.imp fun n => Option.isSome_iff_exists.2
    have s := Nat.find_spec h'
    have fd : (rfind fun n => (f n).isSome).Dom :=
      ⟨Nat.find h', by simpa using s.symm, fun _ _ => trivial⟩
    refine ⟨fd, ?_⟩
    have := rfind_spec (get_mem fd)
    simpa using this⟩

/--
theorem `rfindOpt_mono` / 定理 `rfindOpt_mono`

English:
theorem rfindOpt_mono
  given: {α} {f : Nat -> Option α} (H : forall {a m n}, m <= n -> a in f m -> a in f n) {a}
  proof: ⟨rfindOpt_spec, fun ⟨n, h⟩ => by
    have h' := rfindOpt_dom.2 ⟨_, _, h⟩
    obtain ⟨k, hk⟩ := rfindOpt_spec ⟨h', rfl⟩
    have := (H (le_max_left _ _) h).symm.trans (H (le_max_right _ _) hk)
    simp at this; simp [this, get_mem]⟩

中文:
定理 rfindOpt_mono
  条件: {α} {f : 自然数 -> 选项类型 α} (H : 对任意 {a m n}, m <= n -> a in f m -> a in f n) {a}
  证明: ⟨rfindOpt_spec, fun ⟨n, h⟩ => by
    have h' := rfindOpt_dom.2 ⟨_, _, h⟩
    obtain ⟨k, hk⟩ := rfindOpt_spec ⟨h', rfl⟩
    have := (H (le_max_left _ _) h).symm.trans (H (le_max_right _ _) hk)
    simp at this; simp [this, get_mem]⟩

Depends on / 依赖: get_mem, le_max_left, le_max_right, rfindOpt_dom, rfindOpt_spec, symm.trans
-/
theorem rfindOpt_mono {α} {f : Nat -> Option α} (H : forall {a m n}, m <= n -> a in f m -> a in f n) {a} :
    a in rfindOpt f ↔ exists n, a in f n :=
  ⟨rfindOpt_spec, fun ⟨n, h⟩ => by
    have h' := rfindOpt_dom.2 ⟨_, _, h⟩
    obtain ⟨k, hk⟩ := rfindOpt_spec ⟨h', rfl⟩
    have := (H (le_max_left _ _) h).symm.trans (H (le_max_right _ _) hk)
    simp at this; simp [this, get_mem]⟩

/--
Inductive type `Partrec` / 归纳类型 `Partrec`

English:
inductive Partrec
  parameters: : (Nat ->. Nat) -> Prop
  constructors (4):
    - zero: Nat.Partrec (pure 0)
    - succ: Nat.Partrec succ
    - left: Nat.Partrec ↑fun n : Nat => n.unpair.1
    - right: Nat.Partrec ↑fun n : Nat => n.unpair.2

中文:
归纳类型 Partrec
  参数: : (自然数 ->. 自然数) -> 命题
  构造子 (4 个):
    - zero: 自然数.Partrec (pure 0)
    - succ: 自然数.Partrec succ
    - left: 自然数.Partrec ↑fun n : 自然数 => n.unpair.1
    - right: 自然数.Partrec ↑fun n : 自然数 => n.unpair.2
-/
protected inductive Partrec : (Nat ->. Nat) -> Prop
  | zero : Nat.Partrec (pure 0)
  | succ : Nat.Partrec succ
  | left : Nat.Partrec ↑fun n : Nat => n.unpair.1
  | right : Nat.Partrec ↑fun n : Nat => n.unpair.2
| pair {f g} : Nat.Partrec f -> Nat.Partrec g -> Nat.Partrec fun n => pair < > f n <*> g n
  | comp {f g} : Nat.Partrec f -> Nat.Partrec g -> Nat.Partrec fun n => g n >>= f
  | prec {f g} : Nat.Partrec f -> Nat.Partrec g -> Nat.Partrec (unpaired fun a n =>
      n.rec (f a) fun y IH => do let i ← IH; g (pair a (pair y i)))
  | rfind {f} : Nat.Partrec f ->
Nat.Partrec fun a => rfind fun n => (fun m => m = 0) < > f (pair a n)

namespace Partrec

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : forall n, f n = g n)
  statement: Nat.Partrec g
  proof: (funext H : f = g) ▸ hf

中文:
定理 of_eq
  条件: {f g : 自然数 ->. 自然数} (hf : 自然数.Partrec f) (H : 对任意 n, f n = g n)
  结论: 自然数.Partrec g
  证明: (funext H : f = g) ▸ hf
-/
theorem of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : forall n, f n = g n) : Nat.Partrec g :=
  (funext H : f = g) ▸ hf

/--
theorem `of_eq_tot` / 定理 `of_eq_tot`

English:
theorem of_eq_tot
  given: {f : Nat ->. Nat} {g : Nat -> Nat} (hf : Nat.Partrec f) (H : forall n, g n in f n)
  proof: hf.of_eq fun n => eq_some_iff.2 (H n)

中文:
定理 of_eq_tot
  条件: {f : 自然数 ->. 自然数} {g : 自然数 -> 自然数} (hf : 自然数.Partrec f) (H : 对任意 n, g n in f n)
  证明: hf.of_eq fun n => eq_some_iff.2 (H n)

Depends on / 依赖: eq_some_iff, hf.of_eq, of_eq
-/
theorem of_eq_tot {f : Nat ->. Nat} {g : Nat -> Nat} (hf : Nat.Partrec f) (H : forall n, g n in f n) :
    Nat.Partrec g :=
  hf.of_eq fun n => eq_some_iff.2 (H n)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `of_primrec` / 定理 `of_primrec`

English:
theorem of_primrec
  given: {f : Nat -> Nat} (hf : Nat.Primrec f)
  statement: Nat.Partrec f
  proof: by
  induction hf with
  | zero => exact zero
  | succ => exact succ
  | left => exact left
  | right => exact right
  | pair _ _ pf pg =>
    refine (pf.pair pg).of_eq_tot fun n => ?_
    simp [Seq.seq]
  | comp _ _ pf pg =>
    refine (pf.comp pg).of_eq_tot fun n => (by simp)
  | prec _ _ pf pg =>

中文:
定理 of_primrec
  条件: {f : 自然数 -> 自然数} (hf : 自然数.Primrec f)
  结论: 自然数.Partrec f
  证明: by
  induction hf with
  | zero => exact zero
  | succ => exact succ
  | left => exact left
  | right => exact right
  | pair _ _ pf pg =>
    refine (pf.pair pg).of_eq_tot fun n => ?_
    simp [Seq.seq]
  | comp _ _ pf pg =>
    refine (pf.comp pg).of_eq_tot fun n => (by simp)
  | prec _ _ pf pg =>

Depends on / 依赖: PFun.coe_val, Seq.seq, bind_eq_bind, coe_val, mem_bind_iff, mem_some_iff, n.unpair, of_eq_tot, pf.comp, pf.pair, pf.prec, unpair, unpaired
-/
theorem of_primrec {f : Nat -> Nat} (hf : Nat.Primrec f) : Nat.Partrec f := by
  induction hf with
  | zero => exact zero
  | succ => exact succ
  | left => exact left
  | right => exact right
  | pair _ _ pf pg =>
    refine (pf.pair pg).of_eq_tot fun n => ?_
    simp [Seq.seq]
  | comp _ _ pf pg =>
    refine (pf.comp pg).of_eq_tot fun n => (by simp)
  | prec _ _ pf pg =>
    refine (pf.prec pg).of_eq_tot fun n => ?_
    simp only [unpaired, PFun.coe_val, bind_eq_bind]
    induction n.unpair.2 with
    | zero => simp
    | succ m IH =>
      simp only [mem_bind_iff, mem_some_iff]
      exact ⟨_, IH, rfl⟩

/--
theorem `some` / 定理 `some`

English:
theorem some
  statement: Nat.Partrec some
  proof: of_primrec Primrec.id

中文:
定理 some
  结论: 自然数.Partrec some
  证明: of_primrec Primrec.id
-/
protected theorem some : Nat.Partrec some :=
  of_primrec Primrec.id

set_option backward.isDefEq.respectTransparency false in
/--
theorem `none` / 定理 `none`

English:
theorem none
  statement: Nat.Partrec fun _ => none
  proof: (of_primrec (Nat.Primrec.const 1)).rfind.of_eq fun _ =>
    eq_none_iff.2 fun _ ⟨h, _⟩ => by simp at h

中文:
定理 none
  结论: 自然数.Partrec fun _ => none
  证明: (of_primrec (Nat.Primrec.const 1)).rfind.of_eq fun _ =>
    eq_none_iff.2 fun _ ⟨h, _⟩ => by simp at h

Depends on / 依赖: Nat.Primrec.const, Primrec, eq_none_iff, of_eq, of_primrec, rfind.of_eq
-/
theorem none : Nat.Partrec fun _ => none :=
  (of_primrec (Nat.Primrec.const 1)).rfind.of_eq fun _ =>
    eq_none_iff.2 fun _ ⟨h, _⟩ => by simp at h

/--
theorem `prec'` / 定理 `prec'`

English:
theorem prec'
  given: {f g h} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hh : Nat.Partrec h)
  proof: ((prec hg hh).comp (pair Partrec.some hf)).of_eq fun a =>
    ext fun s => by simp [Seq.seq]

中文:
定理 prec'
  条件: {f g h} (hf : 自然数.Partrec f) (hg : 自然数.Partrec g) (hh : 自然数.Partrec h)
  证明: ((prec hg hh).comp (pair Partrec.some hf)).of_eq fun a =>
    ext fun s => by simp [Seq.seq]

Depends on / 依赖: Partrec, Partrec.some, Seq.seq, of_eq
-/
theorem prec' {f g h} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hh : Nat.Partrec h) :
    Nat.Partrec fun a => (f a).bind fun n => n.rec (g a)
      fun y IH => do {let i ← IH; h (Nat.pair a (Nat.pair y i))} :=
  ((prec hg hh).comp (pair Partrec.some hf)).of_eq fun a =>
    ext fun s => by simp [Seq.seq]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ppred` / 定理 `ppred`

English:
theorem ppred
  statement: Nat.Partrec fun n => ppred n
  proof: have : Primrec₂ fun n m => if n = Nat.succ m then 0 else 1 :=
    (Primrec.ite
      (@PrimrecRel.comp _ _ _ _ _ _ _ _ _
        Primrec.eq Primrec.fst (_root_.Primrec.succ.comp Primrec.snd))
      (_root_.Primrec.const 0) (_root_.Primrec.const 1)).to₂
  (of_primrec (Primrec₂.unpaired'.2 this)).rfin

中文:
定理 ppred
  结论: 自然数.Partrec fun n => ppred n
  证明: have : Primrec₂ fun n m => if n = Nat.succ m then 0 else 1 :=
    (Primrec.ite
      (@PrimrecRel.comp _ _ _ _ _ _ _ _ _
        Primrec.eq Primrec.fst (_root_.Primrec.succ.comp Primrec.snd))
      (_root_.Primrec.const 0) (_root_.Primrec.const 1)).to₂
  (of_primrec (Primrec₂.unpaired'.2 this)).rfin

Depends on / 依赖: Nat.succ, Primrec, Primrec.eq, Primrec.fst, Primrec.ite, Primrec.snd, PrimrecRel, PrimrecRel.comp, _root_, _root_.Primrec.const, _root_.Primrec.succ.comp, eq_none_iff, eq_some_iff, of_eq, of_primrec, rfind.of_eq, unpaired
-/
theorem ppred : Nat.Partrec fun n => ppred n :=
  have : Primrec₂ fun n m => if n = Nat.succ m then 0 else 1 :=
    (Primrec.ite
      (@PrimrecRel.comp _ _ _ _ _ _ _ _ _
        Primrec.eq Primrec.fst (_root_.Primrec.succ.comp Primrec.snd))
      (_root_.Primrec.const 0) (_root_.Primrec.const 1)).to₂
  (of_primrec (Primrec₂.unpaired'.2 this)).rfind.of_eq fun n => by
    cases n
    · exact eq_none_iff.2 (by simp)
    · exact eq_some_iff.2 (by simp; lia)

end Partrec

end Nat

/--
Definition of `Partrec` / `Partrec` 的定义

English:
definition Partrec
  signature: {α σ} [Primcodable α] [Primcodable σ] (f : α ->. σ)
  body: Nat.Partrec fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

中文:
定义 Partrec
  签名: {α σ} [Primcodable α] [Primcodable σ] (f : α ->. σ)
  定义体: Nat.Partrec fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

Depends on / 依赖: Nat.Partrec, Part.bind, Partrec, decode, encode
-/
def Partrec {α σ} [Primcodable α] [Primcodable σ] (f : α ->. σ) :=
  Nat.Partrec fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

/--
Definition of `Partrec₂` / `Partrec₂` 的定义

English:
definition Partrec₂
  signature: {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α -> β ->. σ)
  body: Partrec fun p : α × β => f p.1 p.2

中文:
定义 Partrec₂
  签名: {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α -> β ->. σ)
  定义体: Partrec fun p : α × β => f p.1 p.2

Depends on / 依赖: Partrec
-/
def Partrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α -> β ->. σ) :=
  Partrec fun p : α × β => f p.1 p.2

/-- Computable functions `α → σ` between `Primcodable` types:
  a function is computable if and only if it is partially recursive (as a partial function) -/
@[wikidata Q1148456]
/--
Definition of `Computable` / `Computable` 的定义

English:
definition Computable
  signature: {α σ} [Primcodable α] [Primcodable σ] (f : α -> σ)
  body: Partrec (f : α ->. σ)

中文:
定义 可计算
  签名: {α σ} [Primcodable α] [Primcodable σ] (f : α -> σ)
  定义体: Partrec (f : α ->. σ)

Depends on / 依赖: Partrec
-/
def Computable {α σ} [Primcodable α] [Primcodable σ] (f : α -> σ) :=
  Partrec (f : α ->. σ)

/--
Definition of `Computable₂` / `Computable₂` 的定义

English:
definition Computable₂
  signature: {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α -> β -> σ)
  body: Computable fun p : α × β => f p.1 p.2

中文:
定义 Computable₂
  签名: {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α -> β -> σ)
  定义体: Computable fun p : α × β => f p.1 p.2

Depends on / 依赖: Computable
-/
def Computable₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α -> β -> σ) :=
  Computable fun p : α × β => f p.1 p.2

/--
theorem `Primrec.to_comp` / 定理 `Primrec.to_comp`

English:
theorem Primrec.to_comp
  given: {α σ} [Primcodable α] [Primcodable σ] {f : α -> σ} (hf : Primrec f)
  proof: (Nat.Partrec.ppred.comp (Nat.Partrec.of_primrec hf)).of_eq fun n => by
    simp; cases decode (α := α) n <;> simp

nonrec theorem Primrec₂.to_comp {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α -> β -> σ} (hf : Primrec₂ f) : Computable₂ f :=
  hf.to_comp

中文:
定理 Primrec.to_comp
  条件: {α σ} [Primcodable α] [Primcodable σ] {f : α -> σ} (hf : Primrec f)
  证明: (Nat.Partrec.ppred.comp (Nat.Partrec.of_primrec hf)).of_eq fun n => by
    simp; cases decode (α := α) n <;> simp

nonrec theorem Primrec₂.to_comp {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α -> β -> σ} (hf : Primrec₂ f) : Computable₂ f :=
  hf.to_comp

Depends on / 依赖: Nat.Partrec.of_primrec, Nat.Partrec.ppred.comp, Partrec, decode, of_eq, of_primrec
-/
theorem Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {f : α -> σ} (hf : Primrec f) :
    Computable f :=
  (Nat.Partrec.ppred.comp (Nat.Partrec.of_primrec hf)).of_eq fun n => by
    simp; cases decode (α := α) n <;> simp

nonrec theorem Primrec₂.to_comp {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α -> β -> σ} (hf : Primrec₂ f) : Computable₂ f :=
  hf.to_comp

/--
theorem `Computable.partrec` / 定理 `Computable.partrec`

English:
theorem Computable.partrec
  statement: {α σ} [Primcodable α] [Primcodable σ] {f : α -> σ}
  proof: hf

中文:
定理 可计算.partrec
  结论: {α σ} [Primcodable α] [Primcodable σ] {f : α -> σ}
  证明: hf
-/
protected theorem Computable.partrec {α σ} [Primcodable α] [Primcodable σ] {f : α -> σ}
    (hf : Computable f) : Partrec (f : α ->. σ) :=
  hf

/--
theorem `Computable₂.partrec₂` / 定理 `Computable₂.partrec₂`

English:
theorem Computable₂.partrec₂
  statement: {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
  proof: hf

中文:
定理 Computable₂.partrec₂
  结论: {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
  证明: hf
-/
protected theorem Computable₂.partrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α -> β -> σ} (hf : Computable₂ f) : Partrec₂ fun a => (f a : β ->. σ) :=
  hf

namespace Computable

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: {f g : α -> σ} (hf : Computable f) (H : forall n, f n = g n)
  statement: Computable g
  proof: (funext H : f = g) ▸ hf

中文:
定理 of_eq
  条件: {f g : α -> σ} (hf : 可计算 f) (H : 对任意 n, f n = g n)
  结论: 可计算 g
  证明: (funext H : f = g) ▸ hf
-/
theorem of_eq {f g : α -> σ} (hf : Computable f) (H : forall n, f n = g n) : Computable g :=
  (funext H : f = g) ▸ hf

/--
theorem `const` / 定理 `const`

English:
theorem const
  given: (s : σ)
  statement: Computable fun _ : α => s
  proof: (Primrec.const _).to_comp

中文:
定理 const
  条件: (s : σ)
  结论: 可计算 fun _ : α => s
  证明: (Primrec.const _).to_comp

Depends on / 依赖: Primrec, Primrec.const, to_comp
-/
theorem const (s : σ) : Computable fun _ : α => s :=
  (Primrec.const _).to_comp

/--
theorem `ofOption` / 定理 `ofOption`

English:
theorem ofOption
  given: {f : α -> Option β} (hf : Computable f)
  statement: Partrec fun a => (f a : Part β)
  proof: (Nat.Partrec.ppred.comp hf).of_eq fun n => by
    rcases decode (α := α) n with - | a <;> simp
    cases f a <;> simp

中文:
定理 ofOption
  条件: {f : α -> 选项类型 β} (hf : 可计算 f)
  结论: Partrec fun a => (f a : Part β)
  证明: (Nat.Partrec.ppred.comp hf).of_eq fun n => by
    rcases decode (α := α) n with - | a <;> simp
    cases f a <;> simp

Depends on / 依赖: Nat.Partrec.ppred.comp, Partrec, decode, of_eq
-/
theorem ofOption {f : α -> Option β} (hf : Computable f) : Partrec fun a => (f a : Part β) :=
  (Nat.Partrec.ppred.comp hf).of_eq fun n => by
    rcases decode (α := α) n with - | a <;> simp
    cases f a <;> simp

/--
theorem `to₂` / 定理 `to₂`

English:
theorem to₂
  given: {f : α × β -> σ} (hf : Computable f)
  statement: Computable₂ fun a b => f (a, b)
  proof: hf.of_eq fun ⟨_, _⟩ => rfl

中文:
定理 to₂
  条件: {f : α × β -> σ} (hf : 可计算 f)
  结论: Computable₂ fun a b => f (a, b)
  证明: hf.of_eq fun ⟨_, _⟩ => rfl

Depends on / 依赖: hf.of_eq, of_eq
-/
theorem to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ fun a b => f (a, b) :=
  hf.of_eq fun ⟨_, _⟩ => rfl

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: Computable (@id α)
  proof: Primrec.id.to_comp

中文:
定理 id
  结论: 可计算 (@id α)
  证明: Primrec.id.to_comp
-/
protected theorem id : Computable (@id α) :=
  Primrec.id.to_comp

/--
theorem `fst` / 定理 `fst`

English:
theorem fst
  statement: Computable (@Prod.fst α β)
  proof: Primrec.fst.to_comp

中文:
定理 fst
  结论: 可计算 (@积类型.fst α β)
  证明: Primrec.fst.to_comp

Depends on / 依赖: Primrec, Primrec.fst.to_comp, to_comp
-/
theorem fst : Computable (@Prod.fst α β) :=
  Primrec.fst.to_comp

/--
theorem `snd` / 定理 `snd`

English:
theorem snd
  statement: Computable (@Prod.snd α β)
  proof: Primrec.snd.to_comp

nonrec theorem pair {f : α -> β} {g : α -> γ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a, g a) :=
  (hf.pair hg).of_eq fun n => by cases decode (α := α) n <;> simp [Seq.seq]

中文:
定理 snd
  结论: 可计算 (@积类型.snd α β)
  证明: Primrec.snd.to_comp

nonrec theorem pair {f : α -> β} {g : α -> γ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a, g a) :=
  (hf.pair hg).of_eq fun n => by cases decode (α := α) n <;> simp [Seq.seq]

Depends on / 依赖: Primrec, Primrec.snd.to_comp, to_comp
-/
theorem snd : Computable (@Prod.snd α β) :=
  Primrec.snd.to_comp

nonrec theorem pair {f : α -> β} {g : α -> γ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a, g a) :=
  (hf.pair hg).of_eq fun n => by cases decode (α := α) n <;> simp [Seq.seq]

/--
theorem `unpair` / 定理 `unpair`

English:
theorem unpair
  statement: Computable Nat.unpair
  proof: Primrec.unpair.to_comp

中文:
定理 unpair
  结论: 可计算 自然数.unpair
  证明: Primrec.unpair.to_comp

Depends on / 依赖: Primrec, Primrec.unpair.to_comp, to_comp, unpair
-/
theorem unpair : Computable Nat.unpair :=
  Primrec.unpair.to_comp

/--
theorem `succ` / 定理 `succ`

English:
theorem succ
  statement: Computable Nat.succ
  proof: Primrec.succ.to_comp

中文:
定理 succ
  结论: 可计算 自然数.succ
  证明: Primrec.succ.to_comp

Depends on / 依赖: Primrec, Primrec.succ.to_comp, to_comp
-/
theorem succ : Computable Nat.succ :=
  Primrec.succ.to_comp

/--
theorem `pred` / 定理 `pred`

English:
theorem pred
  statement: Computable Nat.pred
  proof: Primrec.pred.to_comp

中文:
定理 pred
  结论: 可计算 自然数.pred
  证明: Primrec.pred.to_comp

Depends on / 依赖: Primrec, Primrec.pred.to_comp, to_comp
-/
theorem pred : Computable Nat.pred :=
  Primrec.pred.to_comp

/--
theorem `nat_bodd` / 定理 `nat_bodd`

English:
theorem nat_bodd
  statement: Computable Nat.bodd
  proof: Primrec.nat_bodd.to_comp

中文:
定理 nat_bodd
  结论: 可计算 自然数.bodd
  证明: Primrec.nat_bodd.to_comp

Depends on / 依赖: Primrec, Primrec.nat_bodd.to_comp, nat_bodd, to_comp
-/
theorem nat_bodd : Computable Nat.bodd :=
  Primrec.nat_bodd.to_comp

/--
theorem `nat_div2` / 定理 `nat_div2`

English:
theorem nat_div2
  statement: Computable Nat.div2
  proof: Primrec.nat_div2.to_comp

中文:
定理 nat_div2
  结论: 可计算 自然数.div2
  证明: Primrec.nat_div2.to_comp

Depends on / 依赖: Primrec, Primrec.nat_div2.to_comp, nat_div2, to_comp
-/
theorem nat_div2 : Computable Nat.div2 :=
  Primrec.nat_div2.to_comp

/--
theorem `sumInl` / 定理 `sumInl`

English:
theorem sumInl
  statement: Computable (@Sum.inl α β)
  proof: Primrec.sumInl.to_comp

中文:
定理 sumInl
  结论: 可计算 (@和.inl α β)
  证明: Primrec.sumInl.to_comp

Depends on / 依赖: Primrec, Primrec.sumInl.to_comp, sumInl, to_comp
-/
theorem sumInl : Computable (@Sum.inl α β) :=
  Primrec.sumInl.to_comp

/--
theorem `sumInr` / 定理 `sumInr`

English:
theorem sumInr
  statement: Computable (@Sum.inr α β)
  proof: Primrec.sumInr.to_comp

中文:
定理 sumInr
  结论: 可计算 (@和.inr α β)
  证明: Primrec.sumInr.to_comp

Depends on / 依赖: Primrec, Primrec.sumInr.to_comp, sumInr, to_comp
-/
theorem sumInr : Computable (@Sum.inr α β) :=
  Primrec.sumInr.to_comp

/--
theorem `list_cons` / 定理 `list_cons`

English:
theorem list_cons
  statement: Computable₂ (@List.cons α)
  proof: Primrec.list_cons.to_comp

中文:
定理 list_cons
  结论: Computable₂ (@列表.cons α)
  证明: Primrec.list_cons.to_comp

Depends on / 依赖: Primrec, Primrec.list_cons.to_comp, list_cons, to_comp
-/
theorem list_cons : Computable₂ (@List.cons α) :=
  Primrec.list_cons.to_comp

/--
theorem `list_reverse` / 定理 `list_reverse`

English:
theorem list_reverse
  statement: Computable (@List.reverse α)
  proof: Primrec.list_reverse.to_comp

中文:
定理 list_reverse
  结论: 可计算 (@列表.reverse α)
  证明: Primrec.list_reverse.to_comp

Depends on / 依赖: Primrec, Primrec.list_reverse.to_comp, list_reverse, to_comp
-/
theorem list_reverse : Computable (@List.reverse α) :=
  Primrec.list_reverse.to_comp

/--
theorem `list_getElem?` / 定理 `list_getElem?`

English:
theorem list_getElem?
  statement: Computable₂ ((·[·]? : List α -> Nat -> Option α))
  proof: Primrec.list_getElem?.to_comp

中文:
定理 list_getElem?
  结论: Computable₂ ((·[·]? : 列表 α -> 自然数 -> 选项类型 α))
  证明: Primrec.list_getElem?.to_comp

Depends on / 依赖: Primrec, Primrec.list_getElem, list_getElem, to_comp
-/
theorem list_getElem? : Computable₂ ((·[·]? : List α -> Nat -> Option α)) :=
  Primrec.list_getElem?.to_comp

/--
theorem `list_append` / 定理 `list_append`

English:
theorem list_append
  statement: Computable₂ ((· ++ ·) : List α -> List α -> List α)
  proof: Primrec.list_append.to_comp

中文:
定理 list_append
  结论: Computable₂ ((· ++ ·) : 列表 α -> 列表 α -> 列表 α)
  证明: Primrec.list_append.to_comp

Depends on / 依赖: Primrec, Primrec.list_append.to_comp, list_append, to_comp
-/
theorem list_append : Computable₂ ((· ++ ·) : List α -> List α -> List α) :=
  Primrec.list_append.to_comp

/--
theorem `list_concat` / 定理 `list_concat`

English:
theorem list_concat
  statement: Computable₂ fun l (a : α) => l ++ [a]
  proof: Primrec.list_concat.to_comp

中文:
定理 list_concat
  结论: Computable₂ fun l (a : α) => l ++ [a]
  证明: Primrec.list_concat.to_comp

Depends on / 依赖: Primrec, Primrec.list_concat.to_comp, list_concat, to_comp
-/
theorem list_concat : Computable₂ fun l (a : α) => l ++ [a] :=
  Primrec.list_concat.to_comp

/--
theorem `list_length` / 定理 `list_length`

English:
theorem list_length
  statement: Computable (@List.length α)
  proof: Primrec.list_length.to_comp

中文:
定理 list_length
  结论: 可计算 (@列表.length α)
  证明: Primrec.list_length.to_comp

Depends on / 依赖: Primrec, Primrec.list_length.to_comp, list_length, to_comp
-/
theorem list_length : Computable (@List.length α) :=
  Primrec.list_length.to_comp

/--
theorem `vector_cons` / 定理 `vector_cons`

English:
theorem vector_cons
  given: {n}
  statement: Computable₂ (@List.Vector.cons α n)
  proof: Primrec.vector_cons.to_comp

中文:
定理 vector_cons
  条件: {n}
  结论: Computable₂ (@列表.Vector.cons α n)
  证明: Primrec.vector_cons.to_comp

Depends on / 依赖: Primrec, Primrec.vector_cons.to_comp, to_comp, vector_cons
-/
theorem vector_cons {n} : Computable₂ (@List.Vector.cons α n) :=
  Primrec.vector_cons.to_comp

/--
theorem `vector_toList` / 定理 `vector_toList`

English:
theorem vector_toList
  given: {n}
  statement: Computable (@List.Vector.toList α n)
  proof: Primrec.vector_toList.to_comp

中文:
定理 vector_toList
  条件: {n}
  结论: 可计算 (@列表.Vector.toList α n)
  证明: Primrec.vector_toList.to_comp

Depends on / 依赖: Primrec, Primrec.vector_toList.to_comp, to_comp, vector_toList
-/
theorem vector_toList {n} : Computable (@List.Vector.toList α n) :=
  Primrec.vector_toList.to_comp

/--
theorem `vector_length` / 定理 `vector_length`

English:
theorem vector_length
  given: {n}
  statement: Computable (@List.Vector.length α n)
  proof: Primrec.vector_length.to_comp

中文:
定理 vector_length
  条件: {n}
  结论: 可计算 (@列表.Vector.length α n)
  证明: Primrec.vector_length.to_comp

Depends on / 依赖: Primrec, Primrec.vector_length.to_comp, to_comp, vector_length
-/
theorem vector_length {n} : Computable (@List.Vector.length α n) :=
  Primrec.vector_length.to_comp

/--
theorem `vector_head` / 定理 `vector_head`

English:
theorem vector_head
  given: {n}
  statement: Computable (@List.Vector.head α n)
  proof: Primrec.vector_head.to_comp

中文:
定理 vector_head
  条件: {n}
  结论: 可计算 (@列表.Vector.head α n)
  证明: Primrec.vector_head.to_comp

Depends on / 依赖: DecidableEq, Encodable, Encodable.decidableEqOfEncodable, Primrec, Primrec.vector_head.to_comp, decidableEqOfEncodable, finsuppEquivDFinsupp, ofEquiv, to_comp, vector_head
-/
theorem vector_head {n} : Computable (@List.Vector.head α n) :=
  Primrec.vector_head.to_comp

/--
theorem `vector_tail` / 定理 `vector_tail`

English:
theorem vector_tail
  given: {n}
  statement: Computable (@List.Vector.tail α n)
  proof: Primrec.vector_tail.to_comp

中文:
定理 vector_tail
  条件: {n}
  结论: 可计算 (@列表.Vector.tail α n)
  证明: Primrec.vector_tail.to_comp

Depends on / 依赖: Primrec, Primrec.vector_tail.to_comp, classical, finsuppEquivDFinsupp, finsuppEquivDFinsupp.symm, of_equiv, to_comp, vector_tail
-/
theorem vector_tail {n} : Computable (@List.Vector.tail α n) :=
  Primrec.vector_tail.to_comp

/--
theorem `vector_get` / 定理 `vector_get`

English:
theorem vector_get
  given: {n}
  statement: Computable₂ (@List.Vector.get α n)
  proof: Primrec.vector_get.to_comp

中文:
定理 vector_get
  条件: {n}
  结论: Computable₂ (@列表.Vector.get α n)
  证明: Primrec.vector_get.to_comp

Depends on / 依赖: Primrec, Primrec.vector_get.to_comp, to_comp, vector_get
-/
theorem vector_get {n} : Computable₂ (@List.Vector.get α n) :=
  Primrec.vector_get.to_comp

/--
theorem `vector_ofFn'` / 定理 `vector_ofFn'`

English:
theorem vector_ofFn'
  given: {n}
  statement: Computable (@List.Vector.ofFn α n)
  proof: Primrec.vector_ofFn'.to_comp

中文:
定理 vector_ofFn'
  条件: {n}
  结论: 可计算 (@列表.Vector.ofFn α n)
  证明: Primrec.vector_ofFn'.to_comp

Depends on / 依赖: Primrec, Primrec.vector_ofFn, to_comp, vector_ofFn
-/
theorem vector_ofFn' {n} : Computable (@List.Vector.ofFn α n) :=
  Primrec.vector_ofFn'.to_comp

/--
theorem `fin_app` / 定理 `fin_app`

English:
theorem fin_app
  given: {n}
  statement: Computable₂ (@id (Fin n -> σ))
  proof: Primrec.fin_app.to_comp

中文:
定理 fin_app
  条件: {n}
  结论: Computable₂ (@id (有限集 n -> σ))
  证明: Primrec.fin_app.to_comp

Depends on / 依赖: Primrec, Primrec.fin_app.to_comp, fin_app, to_comp
-/
theorem fin_app {n} : Computable₂ (@id (Fin n -> σ)) :=
  Primrec.fin_app.to_comp

/--
theorem `encode` / 定理 `encode`

English:
theorem encode
  statement: Computable (@encode α _)
  proof: Primrec.encode.to_comp

中文:
定理 encode
  结论: 可计算 (@encode α _)
  证明: Primrec.encode.to_comp
-/
protected theorem encode : Computable (@encode α _) :=
  Primrec.encode.to_comp

/--
theorem `decode` / 定理 `decode`

English:
theorem decode
  statement: Computable (decode (α := α))
  proof: Primrec.decode.to_comp

中文:
定理 decode
  结论: 可计算 (decode (α := α))
  证明: Primrec.decode.to_comp
-/
protected theorem decode : Computable (decode (α := α)) :=
  Primrec.decode.to_comp

/--
theorem `ofNat` / 定理 `ofNat`

English:
theorem ofNat
  given: (α) [Denumerable α]
  statement: Computable (ofNat α)
  proof: (Primrec.ofNat _).to_comp

中文:
定理 of自然数
  条件: (α) [可枚举 α]
  结论: 可计算 (of自然数 α)
  证明: (Primrec.ofNat _).to_comp
-/
protected theorem ofNat (α) [Denumerable α] : Computable (ofNat α) :=
  (Primrec.ofNat _).to_comp

/--
theorem `encode_iff` / 定理 `encode_iff`

English:
theorem encode_iff
  given: {f : α -> σ}
  statement: (Computable fun a => encode (f a)) ↔ Computable f
  proof: Iff.rfl

中文:
定理 encode_iff
  条件: {f : α -> σ}
  结论: (可计算 fun a => encode (f a)) ↔ 可计算 f
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem encode_iff {f : α -> σ} : (Computable fun a => encode (f a)) ↔ Computable f :=
  Iff.rfl

/--
theorem `option_some` / 定理 `option_some`

English:
theorem option_some
  statement: Computable (@Option.some α)
  proof: Primrec.option_some.to_comp

中文:
定理 option_some
  结论: 可计算 (@选项类型.some α)
  证明: Primrec.option_some.to_comp

Depends on / 依赖: Primrec, Primrec.option_some.to_comp, option_some, to_comp
-/
theorem option_some : Computable (@Option.some α) :=
  Primrec.option_some.to_comp

end Computable

namespace Partrec

variable {α : Type*} {β : Type*} {σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

open Computable

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n = g n)
  statement: Partrec g
  proof: (funext H : f = g) ▸ hf

中文:
定理 of_eq
  条件: {f g : α ->. σ} (hf : Partrec f) (H : 对任意 n, f n = g n)
  结论: Partrec g
  证明: (funext H : f = g) ▸ hf
-/
theorem of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n = g n) : Partrec g :=
  (funext H : f = g) ▸ hf

/--
theorem `of_eq_tot` / 定理 `of_eq_tot`

English:
theorem of_eq_tot
  given: {f : α ->. σ} {g : α -> σ} (hf : Partrec f) (H : forall n, g n in f n)
  statement: Computable g
  proof: hf.of_eq fun a => eq_some_iff.2 (H a)

中文:
定理 of_eq_tot
  条件: {f : α ->. σ} {g : α -> σ} (hf : Partrec f) (H : 对任意 n, g n in f n)
  结论: 可计算 g
  证明: hf.of_eq fun a => eq_some_iff.2 (H a)

Depends on / 依赖: eq_some_iff, hf.of_eq, of_eq
-/
theorem of_eq_tot {f : α ->. σ} {g : α -> σ} (hf : Partrec f) (H : forall n, g n in f n) : Computable g :=
  hf.of_eq fun a => eq_some_iff.2 (H a)

/--
theorem `none` / 定理 `none`

English:
theorem none
  statement: Partrec fun _ : α => @Part.none σ
  proof: Nat.Partrec.none.of_eq fun n => by cases decode (α := α) n <;> simp

中文:
定理 none
  结论: Partrec fun _ : α => @Part.none σ
  证明: Nat.Partrec.none.of_eq fun n => by cases decode (α := α) n <;> simp

Depends on / 依赖: Nat.Partrec.none.of_eq, Partrec, decode, of_eq
-/
theorem none : Partrec fun _ : α => @Part.none σ :=
  Nat.Partrec.none.of_eq fun n => by cases decode (α := α) n <;> simp

/--
theorem `some` / 定理 `some`

English:
theorem some
  statement: Partrec (@Part.some α)
  proof: Computable.id

中文:
定理 some
  结论: Partrec (@Part.some α)
  证明: Computable.id
-/
protected theorem some : Partrec (@Part.some α) :=
  Computable.id

/--
theorem `_root_.Decidable.Partrec.const'` / 定理 `_root_.Decidable.Partrec.const'`

English:
theorem _root_.Decidable.Partrec.const'
  given: (s : Part σ) [Decidable s.Dom]
  statement: Partrec fun _ : α => s
  proof: (Computable.ofOption (const (toOption s))).of_eq fun _ => of_toOption s

中文:
定理 _root_.可判定.Partrec.const'
  条件: (s : Part σ) [可判定 s.Dom]
  结论: Partrec fun _ : α => s
  证明: (Computable.ofOption (const (toOption s))).of_eq fun _ => of_toOption s

Depends on / 依赖: Computable, Computable.ofOption, ofOption, of_eq, of_toOption, toOption
-/
theorem _root_.Decidable.Partrec.const' (s : Part σ) [Decidable s.Dom] : Partrec fun _ : α => s :=
  (Computable.ofOption (const (toOption s))).of_eq fun _ => of_toOption s

/--
theorem `const'` / 定理 `const'`

English:
theorem const'
  given: (s : Part σ)
  statement: Partrec fun _ : α => s
  proof: haveI := Classical.dec s.Dom
  Decidable.Partrec.const' s

中文:
定理 const'
  条件: (s : Part σ)
  结论: Partrec fun _ : α => s
  证明: haveI := Classical.dec s.Dom
  Decidable.Partrec.const' s

Depends on / 依赖: Classical, Classical.dec, Decidable, Decidable.Partrec.const, Partrec, s.Dom
-/
theorem const' (s : Part σ) : Partrec fun _ : α => s :=
  haveI := Classical.dec s.Dom
  Decidable.Partrec.const' s

set_option backward.isDefEq.respectTransparency false in
/--
theorem `bind` / 定理 `bind`

English:
theorem bind
  given: {f : α ->. β} {g : α -> β ->. σ} (hf : Partrec f) (hg : Partrec₂ g)
  proof: (hg.comp (Nat.Partrec.some.pair hf)).of_eq fun n => by
    rcases e : decode (α := α) n <;> simp [Seq.seq, e, encodek]

中文:
定理 bind
  条件: {f : α ->. β} {g : α -> β ->. σ} (hf : Partrec f) (hg : Partrec₂ g)
  证明: (hg.comp (Nat.Partrec.some.pair hf)).of_eq fun n => by
    rcases e : decode (α := α) n <;> simp [Seq.seq, e, encodek]
-/
protected theorem bind {f : α ->. β} {g : α -> β ->. σ} (hf : Partrec f) (hg : Partrec₂ g) :
    Partrec fun a => (f a).bind (g a) :=
  (hg.comp (Nat.Partrec.some.pair hf)).of_eq fun n => by
    rcases e : decode (α := α) n <;> simp [Seq.seq, e, encodek]

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: {f : α ->. β} {g : α -> β -> σ} (hf : Partrec f) (hg : Computable₂ g)
  proof: by
  simpa [bind_some_eq_map] using Partrec.bind (g := fun a x => some (g a x)) hf hg

中文:
定理 map
  条件: {f : α ->. β} {g : α -> β -> σ} (hf : Partrec f) (hg : Computable₂ g)
  证明: by
  simpa [bind_some_eq_map] using Partrec.bind (g := fun a x => some (g a x)) hf hg

Depends on / 依赖: Partrec, Partrec.bind, bind_some_eq_map
-/
theorem map {f : α ->. β} {g : α -> β -> σ} (hf : Partrec f) (hg : Computable₂ g) :
    Partrec fun a => (f a).map (g a) := by
  simpa [bind_some_eq_map] using Partrec.bind (g := fun a x => some (g a x)) hf hg

/--
theorem `to₂` / 定理 `to₂`

English:
theorem to₂
  given: {f : α × β ->. σ} (hf : Partrec f)
  statement: Partrec₂ fun a b => f (a, b)
  proof: hf.of_eq fun ⟨_, _⟩ => rfl

中文:
定理 to₂
  条件: {f : α × β ->. σ} (hf : Partrec f)
  结论: Partrec₂ fun a b => f (a, b)
  证明: hf.of_eq fun ⟨_, _⟩ => rfl

Depends on / 依赖: hf.of_eq, of_eq
-/
theorem to₂ {f : α × β ->. σ} (hf : Partrec f) : Partrec₂ fun a b => f (a, b) :=
  hf.of_eq fun ⟨_, _⟩ => rfl

/--
theorem `nat_rec` / 定理 `nat_rec`

English:
theorem nat_rec
  statement: {f : α -> Nat} {g : α ->. σ} {h : α -> Nat × σ ->. σ} (hf : Computable f) (hg : Partrec g)
  proof: (Nat.Partrec.prec' hf hg hh).of_eq fun n => by
    rcases e : decode (α := α) n with - | a
    · simp
    · simp only [coe_some, PFun.coe_val, bind_some]
      induction f a <;> simp_all

nonrec theorem comp {f : β ->. σ} {g : α -> β} (hf : Partrec f) (hg : Computable g) :
    Partrec fun a => f (g 

中文:
定理 nat_rec
  结论: {f : α -> 自然数} {g : α ->. σ} {h : α -> 自然数 × σ ->. σ} (hf : 可计算 f) (hg : Partrec g)
  证明: (Nat.Partrec.prec' hf hg hh).of_eq fun n => by
    rcases e : decode (α := α) n with - | a
    · simp
    · simp only [coe_some, PFun.coe_val, bind_some]
      induction f a <;> simp_all

nonrec theorem comp {f : β ->. σ} {g : α -> β} (hf : Partrec f) (hg : Computable g) :
    Partrec fun a => f (g 

Depends on / 依赖: Nat.Partrec.prec, PFun.coe_val, Partrec, bind_some, coe_some, coe_val, decode, of_eq
-/
theorem nat_rec {f : α -> Nat} {g : α ->. σ} {h : α -> Nat × σ ->. σ} (hf : Computable f) (hg : Partrec g)
    (hh : Partrec₂ h) : Partrec fun a => (f a).rec (g a) fun y IH => IH.bind fun i => h a (y, i) :=
  (Nat.Partrec.prec' hf hg hh).of_eq fun n => by
    rcases e : decode (α := α) n with - | a
    · simp
    · simp only [coe_some, PFun.coe_val, bind_some]
      induction f a <;> simp_all

nonrec theorem comp {f : β ->. σ} {g : α -> β} (hf : Partrec f) (hg : Computable g) :
    Partrec fun a => f (g a) :=
  (hf.comp hg).of_eq fun n => by
    simp only [PFun.coe_val, map_some, bind_eq_bind]
    rcases e : decode (α := α) n with - | a <;> simp [encodek]

/--
theorem `nat_iff` / 定理 `nat_iff`

English:
theorem nat_iff
  given: {f : Nat ->. Nat}
  statement: Partrec f ↔ Nat.Partrec f
  proof: by simp [Partrec, map_id']

中文:
定理 nat_iff
  条件: {f : 自然数 ->. 自然数}
  结论: Partrec f ↔ 自然数.Partrec f
  证明: by simp [Partrec, map_id']

Depends on / 依赖: Partrec, map_id
-/
theorem nat_iff {f : Nat ->. Nat} : Partrec f ↔ Nat.Partrec f := by simp [Partrec, map_id']

/--
theorem `map_encode_iff` / 定理 `map_encode_iff`

English:
theorem map_encode_iff
  given: {f : α ->. σ}
  statement: (Partrec fun a => (f a).map encode) ↔ Partrec f
  proof: Iff.rfl

中文:
定理 map_encode_iff
  条件: {f : α ->. σ}
  结论: (Partrec fun a => (f a).map encode) ↔ Partrec f
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem map_encode_iff {f : α ->. σ} : (Partrec fun a => (f a).map encode) ↔ Partrec f :=
  Iff.rfl

end Partrec

namespace Partrec₂

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

/--
theorem `unpaired` / 定理 `unpaired`

English:
theorem unpaired
  given: {f : Nat -> Nat ->. α}
  statement: Partrec (Nat.unpaired f) ↔ Partrec₂ f
  proof: ⟨fun h => by simpa using! Partrec.comp (g := fun p : Nat × Nat => (p.1, p.2)) h Primrec₂.pair.to_comp,
    fun h => h.comp Primrec.unpair.to_comp⟩

中文:
定理 unpaired
  条件: {f : 自然数 -> 自然数 ->. α}
  结论: Partrec (自然数.unpaired f) ↔ Partrec₂ f
  证明: ⟨fun h => by simpa using! Partrec.comp (g := fun p : Nat × Nat => (p.1, p.2)) h Primrec₂.pair.to_comp,
    fun h => h.comp Primrec.unpair.to_comp⟩

Depends on / 依赖: Partrec, Partrec.comp, Primrec, Primrec.unpair.to_comp, h.comp, pair.to_comp, to_comp, unpair
-/
theorem unpaired {f : Nat -> Nat ->. α} : Partrec (Nat.unpaired f) ↔ Partrec₂ f :=
  ⟨fun h => by simpa using! Partrec.comp (g := fun p : Nat × Nat => (p.1, p.2)) h Primrec₂.pair.to_comp,
    fun h => h.comp Primrec.unpair.to_comp⟩

/--
theorem `unpaired'` / 定理 `unpaired'`

English:
theorem unpaired'
  given: {f : Nat -> Nat ->. Nat}
  statement: Nat.Partrec (Nat.unpaired f) ↔ Partrec₂ f
  proof: Partrec.nat_iff.symm.trans unpaired

nonrec theorem comp {f : β -> γ ->. σ} {g : α -> β} {h : α -> γ} (hf : Partrec₂ f) (hg : Computable g)
    (hh : Computable h) : Partrec fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)

中文:
定理 unpaired'
  条件: {f : 自然数 -> 自然数 ->. 自然数}
  结论: 自然数.Partrec (自然数.unpaired f) ↔ Partrec₂ f
  证明: Partrec.nat_iff.symm.trans unpaired

nonrec theorem comp {f : β -> γ ->. σ} {g : α -> β} {h : α -> γ} (hf : Partrec₂ f) (hg : Computable g)
    (hh : Computable h) : Partrec fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)

Depends on / 依赖: Partrec, Partrec.nat_iff.symm.trans, nat_iff, unpaired
-/
theorem unpaired' {f : Nat -> Nat ->. Nat} : Nat.Partrec (Nat.unpaired f) ↔ Partrec₂ f :=
  Partrec.nat_iff.symm.trans unpaired

nonrec theorem comp {f : β -> γ ->. σ} {g : α -> β} {h : α -> γ} (hf : Partrec₂ f) (hg : Computable g)
    (hh : Computable h) : Partrec fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)

/--
theorem `comp₂` / 定理 `comp₂`

English:
theorem comp₂
  statement: {f : γ -> δ ->. σ} {g : α -> β -> γ} {h : α -> β -> δ} (hf : Partrec₂ f)
  proof: hf.comp hg hh

中文:
定理 comp₂
  结论: {f : γ -> δ ->. σ} {g : α -> β -> γ} {h : α -> β -> δ} (hf : Partrec₂ f)
  证明: hf.comp hg hh

Depends on / 依赖: hf.comp
-/
theorem comp₂ {f : γ -> δ ->. σ} {g : α -> β -> γ} {h : α -> β -> δ} (hf : Partrec₂ f)
    (hg : Computable₂ g) (hh : Computable₂ h) : Partrec₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh

end Partrec₂

namespace Computable

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

nonrec theorem comp {f : β -> σ} {g : α -> β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => f (g a) :=
  hf.comp hg

/--
theorem `comp₂` / 定理 `comp₂`

English:
theorem comp₂
  given: {f : γ -> σ} {g : α -> β -> γ} (hf : Computable f) (hg : Computable₂ g)
  proof: hf.comp hg

中文:
定理 comp₂
  条件: {f : γ -> σ} {g : α -> β -> γ} (hf : 可计算 f) (hg : Computable₂ g)
  证明: hf.comp hg

Depends on / 依赖: hf.comp
-/
theorem comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Computable f) (hg : Computable₂ g) :
    Computable₂ fun a b => f (g a b) :=
  hf.comp hg

end Computable

namespace Computable₂

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

/--
theorem `mk` / 定理 `mk`

English:
theorem mk
  given: {f : α -> β -> σ} (hf : Computable fun p : α × β => f p.1 p.2)
  statement: Computable₂ f
  proof: hf

nonrec theorem comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ} (hf : Computable₂ f)
    (hg : Computable g) (hh : Computable h) : Computable fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)

中文:
定理 mk
  条件: {f : α -> β -> σ} (hf : 可计算 fun p : α × β => f p.1 p.2)
  结论: Computable₂ f
  证明: hf

nonrec theorem comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ} (hf : Computable₂ f)
    (hg : Computable g) (hh : Computable h) : Computable fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)
-/
theorem mk {f : α -> β -> σ} (hf : Computable fun p : α × β => f p.1 p.2) : Computable₂ f := hf

nonrec theorem comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ} (hf : Computable₂ f)
    (hg : Computable g) (hh : Computable h) : Computable fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)

/--
theorem `comp₂` / 定理 `comp₂`

English:
theorem comp₂
  statement: {f : γ -> δ -> σ} {g : α -> β -> γ} {h : α -> β -> δ} (hf : Computable₂ f)
  proof: hf.comp hg hh

中文:
定理 comp₂
  结论: {f : γ -> δ -> σ} {g : α -> β -> γ} {h : α -> β -> δ} (hf : Computable₂ f)
  证明: hf.comp hg hh

Depends on / 依赖: hf.comp
-/
theorem comp₂ {f : γ -> δ -> σ} {g : α -> β -> γ} {h : α -> β -> δ} (hf : Computable₂ f)
    (hg : Computable₂ g) (hh : Computable₂ h) : Computable₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh

end Computable₂

namespace Partrec

variable {α : Type*} {σ : Type*} [Primcodable α] [Primcodable σ]

open Computable

set_option backward.isDefEq.respectTransparency false in
/--
theorem `rfind` / 定理 `rfind`

English:
theorem rfind
  given: {p : α -> Nat ->. Bool} (hp : Partrec₂ p)
  statement: Partrec fun a => Nat.rfind (p a)
  proof: (Nat.Partrec.rfind <|
        hp.map ((Primrec.dom_bool fun b => cond b 0 1).comp Primrec.snd).to₂.to_comp).of_eq
    fun n => by
    rcases e : decode (α := α) n <;> simp [e, Nat.rfind_zero_none, map_map, map_id']

中文:
定理 rfind
  条件: {p : α -> 自然数 ->. 布尔值} (hp : Partrec₂ p)
  结论: Partrec fun a => 自然数.rfind (p a)
  证明: (Nat.Partrec.rfind <|
        hp.map ((Primrec.dom_bool fun b => cond b 0 1).comp Primrec.snd).to₂.to_comp).of_eq
    fun n => by
    rcases e : decode (α := α) n <;> simp [e, Nat.rfind_zero_none, map_map, map_id']

Depends on / 依赖: Nat.Partrec.rfind, Nat.rfind_zero_none, Partrec, Primrec, Primrec.dom_bool, Primrec.snd, decode, dom_bool, hp.map, map_id, map_map, of_eq, rfind_zero_none, to_comp
-/
theorem rfind {p : α -> Nat ->. Bool} (hp : Partrec₂ p) : Partrec fun a => Nat.rfind (p a) :=
  (Nat.Partrec.rfind <|
        hp.map ((Primrec.dom_bool fun b => cond b 0 1).comp Primrec.snd).to₂.to_comp).of_eq
    fun n => by
    rcases e : decode (α := α) n <;> simp [e, Nat.rfind_zero_none, map_map, map_id']

/--
theorem `rfindOpt` / 定理 `rfindOpt`

English:
theorem rfindOpt
  given: {f : α -> Nat -> Option σ} (hf : Computable₂ f)
  proof: (rfind (Primrec.option_isSome.to_comp.comp hf).partrec.to₂).bind (ofOption hf)

中文:
定理 rfindOpt
  条件: {f : α -> 自然数 -> 选项类型 σ} (hf : Computable₂ f)
  证明: (rfind (Primrec.option_isSome.to_comp.comp hf).partrec.to₂).bind (ofOption hf)

Depends on / 依赖: Primrec, Primrec.option_isSome.to_comp.comp, ofOption, option_isSome, partrec, partrec.to, to_comp
-/
theorem rfindOpt {f : α -> Nat -> Option σ} (hf : Computable₂ f) :
    Partrec fun a => Nat.rfindOpt (f a) :=
  (rfind (Primrec.option_isSome.to_comp.comp hf).partrec.to₂).bind (ofOption hf)

/--
theorem `nat_casesOn_right` / 定理 `nat_casesOn_right`

English:
theorem nat_casesOn_right
  statement: {f : α -> Nat} {g : α -> σ} {h : α -> Nat ->. σ} (hf : Computable f)
  proof: (nat_rec hf hg (hh.comp fst (pred.comp <| hf.comp fst)).to₂).of_eq fun a => by
    simp only [PFun.coe_val, Nat.pred_eq_sub_one]
    rcases f a with - | n
    · simp
    · refine ext fun b => ⟨fun H => ?_, fun H => ?_⟩
      · rcases mem_bind_iff.1 H with ⟨c, _, h₂⟩
        exact h₂
      · have : f

中文:
定理 nat_casesOn_right
  结论: {f : α -> 自然数} {g : α -> σ} {h : α -> 自然数 ->. σ} (hf : 可计算 f)
  证明: (nat_rec hf hg (hh.comp fst (pred.comp <| hf.comp fst)).to₂).of_eq fun a => by
    simp only [PFun.coe_val, Nat.pred_eq_sub_one]
    rcases f a with - | n
    · simp
    · refine ext fun b => ⟨fun H => ?_, fun H => ?_⟩
      · rcases mem_bind_iff.1 H with ⟨c, _, h₂⟩
        exact h₂
      · have : f

Depends on / 依赖: H.fst, H.snd, IH.bind, Nat.pred_eq_sub_one, Nat.rec, PFun.coe_val, Part.some, coe_val, hf.comp, hh.comp, mem_bind_iff, motive, nat_rec, of_eq, pred.comp, pred_eq_sub_one
-/
theorem nat_casesOn_right {f : α -> Nat} {g : α -> σ} {h : α -> Nat ->. σ} (hf : Computable f)
    (hg : Computable g) (hh : Partrec₂ h) : Partrec fun a => (f a).casesOn (some (g a)) (h a) :=
  (nat_rec hf hg (hh.comp fst (pred.comp <| hf.comp fst)).to₂).of_eq fun a => by
    simp only [PFun.coe_val, Nat.pred_eq_sub_one]
    rcases f a with - | n
    · simp
    · refine ext fun b => ⟨fun H => ?_, fun H => ?_⟩
      · rcases mem_bind_iff.1 H with ⟨c, _, h₂⟩
        exact h₂
      · have : forall m, (Nat.rec (motive := fun _ => Part σ)
            (Part.some (g a)) (fun y IH => IH.bind fun _ => h a n) m).Dom := by
          intro m
          induction m <;> simp [*, H.fst]
        exact ⟨⟨this n, H.fst⟩, H.snd⟩

/--
theorem `bind_decode₂_iff` / 定理 `bind_decode₂_iff`

English:
theorem bind_decode₂_iff
  given: {f : α ->. σ}
  proof: ⟨fun hf =>
nat_iff.1
(Computable.ofOption Primrec.decode₂.to_comp).bind
        (map hf (Computable.encode.comp snd).to₂).comp snd,
    fun h =>
map_encode_iff.1 by simpa [encodek₂] using (nat_iff.2 h).comp (@Computable.encode α _)⟩

中文:
定理 bind_decode₂_iff
  条件: {f : α ->. σ}
  证明: ⟨fun hf =>
nat_iff.1
(Computable.ofOption Primrec.decode₂.to_comp).bind
        (map hf (Computable.encode.comp snd).to₂).comp snd,
    fun h =>
map_encode_iff.1 by simpa [encodek₂] using (nat_iff.2 h).comp (@Computable.encode α _)⟩

Depends on / 依赖: Computable, Computable.encode, Computable.encode.comp, Computable.ofOption, Primrec, Primrec.decode, encode, map_encode_iff, nat_iff, ofOption, to_comp
-/
theorem bind_decode₂_iff {f : α ->. σ} :
    Partrec f ↔ Nat.Partrec fun n => Part.bind (decode₂ α n) fun a => (f a).map encode :=
  ⟨fun hf =>
nat_iff.1
(Computable.ofOption Primrec.decode₂.to_comp).bind
        (map hf (Computable.encode.comp snd).to₂).comp snd,
    fun h =>
map_encode_iff.1 by simpa [encodek₂] using (nat_iff.2 h).comp (@Computable.encode α _)⟩

/--
theorem `vector_mOfFn` / 定理 `vector_mOfFn`

English:
theorem vector_mOfFn

中文:
定理 vector_mOfFn
-/
theorem vector_mOfFn :
    forall {n} {f : Fin n -> α ->. σ},
      (forall i, Partrec (f i)) -> Partrec fun a : α => Vector.mOfFn fun i => f i a
  | 0, _, _ => const _
  | n + 1, f, hf => by
    simp only [Vector.mOfFn, pure_eq_some, bind_eq_bind]
    exact
      (hf 0).bind
        (Partrec.bind ((vector_mOfFn fun i => hf i.succ).comp fst)
          (Primrec.vector_cons.to_comp.comp (snd.comp fst) snd))

end Partrec

@[simp]
/--
theorem `Vector.mOfFn_part_some` / 定理 `Vector.mOfFn_part_some`

English:
theorem Vector.mOfFn_part_some
  given: {α n}
  proof: Vector.mOfFn_pure

中文:
定理 Vector.mOfFn_part_some
  条件: {α n}
  证明: Vector.mOfFn_pure

Depends on / 依赖: Vector, Vector.mOfFn_pure, mOfFn_pure
-/
theorem Vector.mOfFn_part_some {α n} :
    forall f : Fin n -> α,
      (List.Vector.mOfFn fun i => Part.some (f i)) = Part.some (List.Vector.ofFn f) :=
  Vector.mOfFn_pure

namespace Computable

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

/--
theorem `option_some_iff` / 定理 `option_some_iff`

English:
theorem option_some_iff
  given: {f : α -> σ}
  statement: (Computable fun a => Option.some (f a)) ↔ Computable f
  proof: ⟨fun h => encode_iff.1 Primrec.pred.to_comp.comp encode_iff.2 h, option_some.comp⟩

中文:
定理 option_some_iff
  条件: {f : α -> σ}
  结论: (可计算 fun a => 选项类型.some (f a)) ↔ 可计算 f
  证明: ⟨fun h => encode_iff.1 Primrec.pred.to_comp.comp encode_iff.2 h, option_some.comp⟩

Depends on / 依赖: Primrec, Primrec.pred.to_comp.comp, encode_iff, option_some, option_some.comp, to_comp
-/
theorem option_some_iff {f : α -> σ} : (Computable fun a => Option.some (f a)) ↔ Computable f :=
⟨fun h => encode_iff.1 Primrec.pred.to_comp.comp encode_iff.2 h, option_some.comp⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `bind_decode_iff` / 定理 `bind_decode_iff`

English:
theorem bind_decode_iff
  given: {f : α -> β -> Option σ}
  proof: ⟨fun hf =>
    Nat.Partrec.of_eq
      (((Partrec.nat_iff.2
        (Nat.Partrec.ppred.comp <| Nat.Partrec.of_primrec <| Primcodable.prim (α := β))).comp
            snd).bind
        (Computable.comp hf fst).to₂.partrec₂)
      fun n => by
        simp only [decode_prod_val, decode_nat, Option.map_

中文:
定理 bind_decode_iff
  条件: {f : α -> β -> 选项类型 σ}
  证明: ⟨fun hf =>
    Nat.Partrec.of_eq
      (((Partrec.nat_iff.2
        (Nat.Partrec.ppred.comp <| Nat.Partrec.of_primrec <| Primcodable.prim (α := β))).comp
            snd).bind
        (Computable.comp hf fst).to₂.partrec₂)
      fun n => by
        simp only [decode_prod_val, decode_nat, Option.map_
-/
theorem bind_decode_iff {f : α -> β -> Option σ} :
    (Computable₂ fun a n => (decode (α := β) n).bind (f a)) ↔ Computable₂ f :=
  ⟨fun hf =>
    Nat.Partrec.of_eq
      (((Partrec.nat_iff.2
        (Nat.Partrec.ppred.comp <| Nat.Partrec.of_primrec <| Primcodable.prim (α := β))).comp
            snd).bind
        (Computable.comp hf fst).to₂.partrec₂)
      fun n => by
        simp only [decode_prod_val, decode_nat, Option.map_some, PFun.coe_val, bind_eq_bind,
          bind_some, Part.map_bind, map_some]
        cases decode (α := α) n.unpair.1 <;> simp
        cases decode (α := β) n.unpair.2 <;> simp,
    fun hf => by
    have :
      Partrec fun a : α × Nat =>
        (encode (decode (α := β) a.2)).casesOn (some Option.none)
          fun n => Part.map (f a.1) (decode (α := β) n) :=
      Partrec.nat_casesOn_right
        (h := fun (a : α × Nat) (n : Nat) => map (fun b => f a.1 b) (Part.ofOption (decode n)))
        (Primrec.encdec.to_comp.comp snd) (const Option.none)
        ((ofOption (Computable.decode.comp snd)).map (hf.comp (fst.comp <| fst.comp fst) snd).to₂)
    refine this.of_eq fun a => ?_
    simp; cases decode (α := β) a.2 <;> simp [encodek]⟩

/--
theorem `map_decode_iff` / 定理 `map_decode_iff`

English:
theorem map_decode_iff
  given: {f : α -> β -> σ}
  proof: by
  convert! (bind_decode_iff (f := fun a => Option.some ∘ f a)).trans option_some_iff
  apply Option.map_eq_bind

中文:
定理 map_decode_iff
  条件: {f : α -> β -> σ}
  证明: by
  convert! (bind_decode_iff (f := fun a => Option.some ∘ f a)).trans option_some_iff
  apply Option.map_eq_bind

Depends on / 依赖: Option.map_eq_bind, Option.some, bind_decode_iff, convert, map_eq_bind, option_some_iff
-/
theorem map_decode_iff {f : α -> β -> σ} :
    (Computable₂ fun a n => (decode (α := β) n).map (f a)) ↔ Computable₂ f := by
  convert! (bind_decode_iff (f := fun a => Option.some ∘ f a)).trans option_some_iff
  apply Option.map_eq_bind

/--
theorem `nat_rec` / 定理 `nat_rec`

English:
theorem nat_rec
  statement: {f : α -> Nat} {g : α -> σ} {h : α -> Nat × σ -> σ} (hf : Computable f) (hg : Computable g)
  proof: (Partrec.nat_rec hf hg hh.partrec₂).of_eq fun a => by simp; induction f a <;> simp [*]

中文:
定理 nat_rec
  结论: {f : α -> 自然数} {g : α -> σ} {h : α -> 自然数 × σ -> σ} (hf : 可计算 f) (hg : 可计算 g)
  证明: (Partrec.nat_rec hf hg hh.partrec₂).of_eq fun a => by simp; induction f a <;> simp [*]
-/
theorem nat_rec {f : α -> Nat} {g : α -> σ} {h : α -> Nat × σ -> σ} (hf : Computable f) (hg : Computable g)
    (hh : Computable₂ h) :
    Computable fun a => Nat.rec (motive := fun _ => σ) (g a) (fun y IH => h a (y, IH)) (f a) :=
  (Partrec.nat_rec hf hg hh.partrec₂).of_eq fun a => by simp; induction f a <;> simp [*]

/--
theorem `nat_casesOn` / 定理 `nat_casesOn`

English:
theorem nat_casesOn
  statement: {f : α -> Nat} {g : α -> σ} {h : α -> Nat -> σ} (hf : Computable f) (hg : Computable g)
  proof: nat_rec hf hg (hh.comp fst <| fst.comp snd).to₂

中文:
定理 nat_casesOn
  结论: {f : α -> 自然数} {g : α -> σ} {h : α -> 自然数 -> σ} (hf : 可计算 f) (hg : 可计算 g)
  证明: nat_rec hf hg (hh.comp fst <| fst.comp snd).to₂
-/
theorem nat_casesOn {f : α -> Nat} {g : α -> σ} {h : α -> Nat -> σ} (hf : Computable f) (hg : Computable g)
    (hh : Computable₂ h) :
    Computable fun a => Nat.casesOn (motive := fun _ => σ) (f a) (g a) (h a) :=
  nat_rec hf hg (hh.comp fst <| fst.comp snd).to₂

/--
theorem `cond` / 定理 `cond`

English:
theorem cond
  statement: {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Computable c) (hf : Computable f)
  proof: (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl

中文:
定理 cond
  结论: {c : α -> 布尔值} {f : α -> σ} {g : α -> σ} (hc : 可计算 c) (hf : 可计算 f)
  证明: (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl

Depends on / 依赖: encode_iff, hf.comp, nat_casesOn, of_eq
-/
theorem cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Computable c) (hf : Computable f)
    (hg : Computable g) : Computable fun a => cond (c a) (f a) (g a) :=
  (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl

/--
theorem `option_casesOn` / 定理 `option_casesOn`

English:
theorem option_casesOn
  statement: {o : α -> Option β} {f : α -> σ} {g : α -> β -> σ} (ho : Computable o)
  proof: option_some_iff.1
    (nat_casesOn (encode_iff.2 ho) (option_some_iff.2 hf) (map_decode_iff.2 hg)).of_eq fun a => by
      cases o a <;> simp [encodek]

中文:
定理 option_casesOn
  结论: {o : α -> 选项类型 β} {f : α -> σ} {g : α -> β -> σ} (ho : 可计算 o)
  证明: option_some_iff.1
    (nat_casesOn (encode_iff.2 ho) (option_some_iff.2 hf) (map_decode_iff.2 hg)).of_eq fun a => by
      cases o a <;> simp [encodek]

Depends on / 依赖: encode_iff, encodek, map_decode_iff, nat_casesOn, of_eq, option_some_iff
-/
theorem option_casesOn {o : α -> Option β} {f : α -> σ} {g : α -> β -> σ} (ho : Computable o)
    (hf : Computable f) (hg : Computable₂ g) :
    @Computable _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) :=
option_some_iff.1
    (nat_casesOn (encode_iff.2 ho) (option_some_iff.2 hf) (map_decode_iff.2 hg)).of_eq fun a => by
      cases o a <;> simp [encodek]

/--
theorem `option_bind` / 定理 `option_bind`

English:
theorem option_bind
  statement: {f : α -> Option β} {g : α -> β -> Option σ} (hf : Computable f)
  proof: (option_casesOn hf (const Option.none) hg).of_eq fun a => by cases f a <;> rfl

中文:
定理 option_bind
  结论: {f : α -> 选项类型 β} {g : α -> β -> 选项类型 σ} (hf : 可计算 f)
  证明: (option_casesOn hf (const Option.none) hg).of_eq fun a => by cases f a <;> rfl

Depends on / 依赖: Option.none, of_eq, option_casesOn
-/
theorem option_bind {f : α -> Option β} {g : α -> β -> Option σ} (hf : Computable f)
    (hg : Computable₂ g) : Computable fun a => (f a).bind (g a) :=
  (option_casesOn hf (const Option.none) hg).of_eq fun a => by cases f a <;> rfl

/--
theorem `option_map` / 定理 `option_map`

English:
theorem option_map
  given: {f : α -> Option β} {g : α -> β -> σ} (hf : Computable f) (hg : Computable₂ g)
  proof: by
  convert! option_bind hf (option_some.comp₂ hg)
  apply Option.map_eq_bind

中文:
定理 option_map
  条件: {f : α -> 选项类型 β} {g : α -> β -> σ} (hf : 可计算 f) (hg : Computable₂ g)
  证明: by
  convert! option_bind hf (option_some.comp₂ hg)
  apply Option.map_eq_bind

Depends on / 依赖: Option.map_eq_bind, convert, map_eq_bind, option_bind, option_some, option_some.comp
-/
theorem option_map {f : α -> Option β} {g : α -> β -> σ} (hf : Computable f) (hg : Computable₂ g) :
    Computable fun a => (f a).map (g a) := by
  convert! option_bind hf (option_some.comp₂ hg)
  apply Option.map_eq_bind

/--
theorem `option_getD` / 定理 `option_getD`

English:
theorem option_getD
  given: {f : α -> Option β} {g : α -> β} (hf : Computable f) (hg : Computable g)
  proof: (Computable.option_casesOn hf hg (show Computable₂ fun _ b => b from Computable.snd)).of_eq
    fun a => by cases f a <;> rfl

中文:
定理 option_getD
  条件: {f : α -> 选项类型 β} {g : α -> β} (hf : 可计算 f) (hg : 可计算 g)
  证明: (Computable.option_casesOn hf hg (show Computable₂ fun _ b => b from Computable.snd)).of_eq
    fun a => by cases f a <;> rfl

Depends on / 依赖: Computable, Computable.option_casesOn, Computable.snd, of_eq, option_casesOn
-/
theorem option_getD {f : α -> Option β} {g : α -> β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a).getD (g a) :=
  (Computable.option_casesOn hf hg (show Computable₂ fun _ b => b from Computable.snd)).of_eq
    fun a => by cases f a <;> rfl

/--
theorem `subtype_mk` / 定理 `subtype_mk`

English:
theorem subtype_mk
  statement: {f : α -> β} {p : β -> Prop} [DecidablePred p] {h : forall a, p (f a)}
  proof: hf

中文:
定理 subtype_mk
  结论: {f : α -> β} {p : β -> 命题} [DecidablePred p] {h : 对任意 a, p (f a)}
  证明: hf
-/
theorem subtype_mk {f : α -> β} {p : β -> Prop} [DecidablePred p] {h : forall a, p (f a)}
    (hp : PrimrecPred p) (hf : Computable f) :
    @Computable _ _ _ (Primcodable.subtype hp) fun a => (⟨f a, h a⟩ : Subtype p) :=
  hf

/--
theorem `sumCasesOn` / 定理 `sumCasesOn`

English:
theorem sumCasesOn
  statement: {f : α -> β oplus γ} {g : α -> β -> σ} {h : α -> γ -> σ} (hf : Computable f)
  proof: option_some_iff.1
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by
        rcases f a with b | c <;> simp

中文:
定理 sumCasesOn
  结论: {f : α -> β oplus γ} {g : α -> β -> σ} {h : α -> γ -> σ} (hf : 可计算 f)
  证明: option_some_iff.1
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by
        rcases f a with b | c <;> simp

Depends on / 依赖: Computable, Computable.decode.comp, Nat.div2_val, decode, div2_val, encode_iff, nat_bodd, nat_bodd.comp, nat_div2, nat_div2.comp, of_eq, option_map, option_some_iff
-/
theorem sumCasesOn {f : α -> β oplus γ} {g : α -> β -> σ} {h : α -> γ -> σ} (hf : Computable f)
    (hg : Computable₂ g) (hh : Computable₂ h) :
    @Computable _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
option_some_iff.1
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by
        rcases f a with b | c <;> simp [Nat.div2_val]

/--
theorem `nat_strong_rec` / 定理 `nat_strong_rec`

English:
theorem nat_strong_rec
  statement: (f : α -> Nat -> σ) {g : α -> List σ -> Option σ} (hg : Computable₂ g)
  proof: suffices Computable₂ fun a n => (List.range n).map (f a) from
option_some_iff.1
      (list_getElem?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a => by
        simp
option_some_iff.1
    (nat_rec snd (const (Option.some []))
          (to₂ <|
option_bind (snd.comp snd)
to₂
             

中文:
定理 nat_strong_rec
  结论: (f : α -> 自然数 -> σ) {g : α -> 列表 σ -> 选项类型 σ} (hg : Computable₂ g)
  证明: suffices Computable₂ fun a n => (List.range n).map (f a) from
option_some_iff.1
      (list_getElem?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a => by
        simp
option_some_iff.1
    (nat_rec snd (const (Option.some []))
          (to₂ <|
option_bind (snd.comp snd)
to₂
             

Depends on / 依赖: List.range, List.range_succ, Option.some, fst.comp, hg.comp, list_concat, list_concat.comp, list_getElem, nat_rec, of_eq, option_bind, option_map, option_some_iff, range_succ, snd.comp, succ.comp, this.comp
-/
theorem nat_strong_rec (f : α -> Nat -> σ) {g : α -> List σ -> Option σ} (hg : Computable₂ g)
    (H : forall a n, g a ((List.range n).map (f a)) = Option.some (f a n)) : Computable₂ f :=
  suffices Computable₂ fun a n => (List.range n).map (f a) from
option_some_iff.1
      (list_getElem?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a => by
        simp
option_some_iff.1
    (nat_rec snd (const (Option.some []))
          (to₂ <|
option_bind (snd.comp snd)
to₂
                option_map (hg.comp (fst.comp <| fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a => by
      induction a.2 with
      | zero => rfl
      | succ n IH => simp [IH, H, List.range_succ]

/--
theorem `list_ofFn` / 定理 `list_ofFn`

English:
theorem list_ofFn

中文:
定理 list_ofFn
-/
theorem list_ofFn :
    forall {n} {f : Fin n -> α -> σ},
      (forall i, Computable (f i)) -> Computable fun a => List.ofFn fun i => f i a
  | 0, _, _ => by
    simp only [List.ofFn_zero]
    exact const []
  | n + 1, f, hf => by
    simp only [List.ofFn_succ]
    exact list_cons.comp (hf 0) (list_ofFn fun i => hf i.succ)

/--
theorem `vector_ofFn` / 定理 `vector_ofFn`

English:
theorem vector_ofFn
  given: {n} {f : Fin n -> α -> σ} (hf : forall i, Computable (f i))
  proof: (Partrec.vector_mOfFn hf).of_eq fun a => by simp

中文:
定理 vector_ofFn
  条件: {n} {f : 有限集 n -> α -> σ} (hf : 对任意 i, 可计算 (f i))
  证明: (Partrec.vector_mOfFn hf).of_eq fun a => by simp

Depends on / 依赖: Partrec, Partrec.vector_mOfFn, of_eq, vector_mOfFn
-/
theorem vector_ofFn {n} {f : Fin n -> α -> σ} (hf : forall i, Computable (f i)) :
    Computable fun a => List.Vector.ofFn fun i => f i a :=
  (Partrec.vector_mOfFn hf).of_eq fun a => by simp

end Computable

namespace Partrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable

/--
theorem `option_some_iff` / 定理 `option_some_iff`

English:
theorem option_some_iff
  given: {f : α ->. σ}
  statement: (Partrec fun a => (f a).map Option.some) ↔ Partrec f
  proof: ⟨fun h => (Nat.Partrec.ppred.comp h).of_eq fun n => by simp [Part.bind_assoc, bind_some_eq_map],
    fun hf => hf.map (option_some.comp snd).to₂⟩

中文:
定理 option_some_iff
  条件: {f : α ->. σ}
  结论: (Partrec fun a => (f a).map 选项类型.some) ↔ Partrec f
  证明: ⟨fun h => (Nat.Partrec.ppred.comp h).of_eq fun n => by simp [Part.bind_assoc, bind_some_eq_map],
    fun hf => hf.map (option_some.comp snd).to₂⟩

Depends on / 依赖: Nat.Partrec.ppred.comp, Part.bind_assoc, Partrec, bind_assoc, bind_some_eq_map, hf.map, of_eq, option_some, option_some.comp
-/
theorem option_some_iff {f : α ->. σ} : (Partrec fun a => (f a).map Option.some) ↔ Partrec f :=
  ⟨fun h => (Nat.Partrec.ppred.comp h).of_eq fun n => by simp [Part.bind_assoc, bind_some_eq_map],
    fun hf => hf.map (option_some.comp snd).to₂⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `optionCasesOn_right` / 定理 `optionCasesOn_right`

English:
theorem optionCasesOn_right
  statement: {o : α -> Option β} {f : α -> σ} {g : α -> β ->. σ} (ho : Computable o)
  proof: have :
    Partrec fun a : α =>
      Nat.casesOn (encode (o a)) (Part.some (f a)) (fun n => Part.bind (decode (α := β) n) (g a)) :=
    nat_casesOn_right (h := fun a n => Part.bind (ofOption (decode n)) fun b => g a b)
(encode_iff.2 ho) hf.partrec
        ((@Computable.decode β _).comp snd).ofOptio

中文:
定理 optionCasesOn_right
  结论: {o : α -> 选项类型 β} {f : α -> σ} {g : α -> β ->. σ} (ho : 可计算 o)
  证明: have :
    Partrec fun a : α =>
      Nat.casesOn (encode (o a)) (Part.some (f a)) (fun n => Part.bind (decode (α := β) n) (g a)) :=
    nat_casesOn_right (h := fun a n => Part.bind (ofOption (decode n)) fun b => g a b)
(encode_iff.2 ho) hf.partrec
        ((@Computable.decode β _).comp snd).ofOptio

Depends on / 依赖: Computable, Computable.decode, Nat.casesOn, Part.bind, Part.some, Partrec, casesOn, decode, encode, encode_iff, encodek, fst.comp, hf.partrec, hg.comp, nat_casesOn_right, ofOption, ofOption.bind, of_eq, partrec, this.of_eq
-/
theorem optionCasesOn_right {o : α -> Option β} {f : α -> σ} {g : α -> β ->. σ} (ho : Computable o)
    (hf : Computable f) (hg : Partrec₂ g) :
    @Partrec _ σ _ _ fun a => Option.casesOn (o a) (Part.some (f a)) (g a) :=
  have :
    Partrec fun a : α =>
      Nat.casesOn (encode (o a)) (Part.some (f a)) (fun n => Part.bind (decode (α := β) n) (g a)) :=
    nat_casesOn_right (h := fun a n => Part.bind (ofOption (decode n)) fun b => g a b)
(encode_iff.2 ho) hf.partrec
        ((@Computable.decode β _).comp snd).ofOption.bind (hg.comp (fst.comp fst) snd).to₂
  this.of_eq fun a => by rcases o a with - | b <;> simp [encodek]

/--
theorem `sumCasesOn_right` / 定理 `sumCasesOn_right`

English:
theorem sumCasesOn_right
  statement: {f : α -> β oplus γ} {g : α -> β -> σ} {h : α -> γ ->. σ} (hf : Computable f)
  proof: have :
    Partrec fun a =>
      (Option.casesOn (Sum.casesOn (f a) (fun _ => Option.none) Option.some : Option γ)
          (some (Sum.casesOn (f a) (fun b => some (g a b)) fun _ => Option.none)) fun c =>
          (h a c).map Option.some :
        Part (Option σ)) :=
    optionCasesOn_right (g :=

中文:
定理 sumCasesOn_right
  结论: {f : α -> β oplus γ} {g : α -> β -> σ} {h : α -> γ ->. σ} (hf : 可计算 f)
  证明: have :
    Partrec fun a =>
      (Option.casesOn (Sum.casesOn (f a) (fun _ => Option.none) Option.some : Option γ)
          (some (Sum.casesOn (f a) (fun b => some (g a b)) fun _ => Option.none)) fun c =>
          (h a c).map Option.some :
        Part (Option σ)) :=
    optionCasesOn_right (g :=

Depends on / 依赖: Option.casesOn, Option.none, Option.some, Part.map, Partrec, Sum.casesOn, casesOn, optionCasesOn_right, option_som, option_some, option_some.comp, option_some_iff, sumCasesOn
-/
theorem sumCasesOn_right {f : α -> β oplus γ} {g : α -> β -> σ} {h : α -> γ ->. σ} (hf : Computable f)
    (hg : Computable₂ g) (hh : Partrec₂ h) :
    @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (fun b => Part.some (g a b)) (h a) :=
  have :
    Partrec fun a =>
      (Option.casesOn (Sum.casesOn (f a) (fun _ => Option.none) Option.some : Option γ)
          (some (Sum.casesOn (f a) (fun b => some (g a b)) fun _ => Option.none)) fun c =>
          (h a c).map Option.some :
        Part (Option σ)) :=
    optionCasesOn_right (g := fun a n => Part.map Option.some (h a n))
      (sumCasesOn hf (const Option.none).to₂ (option_some.comp snd).to₂)
      (sumCasesOn (g := fun a n => Option.some (g a n)) hf (option_some.comp hg)
        (const Option.none).to₂)
      (option_some_iff.2 hh)
option_some_iff.1 this.of_eq fun a => by cases f a <;> simp

/--
theorem `sumCasesOn_left` / 定理 `sumCasesOn_left`

English:
theorem sumCasesOn_left
  statement: {f : α -> β oplus γ} {g : α -> β ->. σ} {h : α -> γ -> σ} (hf : Computable f)
  proof: (sumCasesOn_right (sumCasesOn hf (sumInr.comp snd).to₂ (sumInl.comp snd).to₂) hh hg).of_eq
    fun a => by cases f a <;> simp

中文:
定理 sumCasesOn_left
  结论: {f : α -> β oplus γ} {g : α -> β ->. σ} {h : α -> γ -> σ} (hf : 可计算 f)
  证明: (sumCasesOn_right (sumCasesOn hf (sumInr.comp snd).to₂ (sumInl.comp snd).to₂) hh hg).of_eq
    fun a => by cases f a <;> simp

Depends on / 依赖: of_eq, sumCasesOn, sumCasesOn_right, sumInl, sumInl.comp, sumInr, sumInr.comp
-/
theorem sumCasesOn_left {f : α -> β oplus γ} {g : α -> β ->. σ} {h : α -> γ -> σ} (hf : Computable f)
    (hg : Partrec₂ g) (hh : Computable₂ h) :
    @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) fun c => Part.some (h a c) :=
  (sumCasesOn_right (sumCasesOn hf (sumInr.comp snd).to₂ (sumInl.comp snd).to₂) hh hg).of_eq
    fun a => by cases f a <;> simp

/--
theorem `fix_aux` / 定理 `fix_aux`

English:
theorem fix_aux
  given: {α σ} (f : α ->. σ oplus α) (a : α) (b : σ)
  proof: fun a n =>
      n.rec (some (Sum.inr a)) fun _ IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
    (exists n : Nat,
        ((exists b' : σ, Sum.inl b' in F a n) ∧ forall {m : Nat}, m < n -> exists b : α, Sum.inr b in F a m) ∧
          Sum.inl b in F a n) ↔
      b in PFun.fix f a :=

中文:
定理 fix_aux
  条件: {α σ} (f : α ->. σ oplus α) (a : α) (b : σ)
  证明: fun a n =>
      n.rec (some (Sum.inr a)) fun _ IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
    (exists n : Nat,
        ((exists b' : σ, Sum.inl b' in F a n) ∧ forall {m : Nat}, m < n -> exists b : α, Sum.inr b in F a m) ∧
          Sum.inl b in F a n) ↔
      b in PFun.fix f a :=
-/
theorem fix_aux {α σ} (f : α ->. σ oplus α) (a : α) (b : σ) :
    let F : α -> Nat ->. σ oplus α := fun a n =>
      n.rec (some (Sum.inr a)) fun _ IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
    (exists n : Nat,
        ((exists b' : σ, Sum.inl b' in F a n) ∧ forall {m : Nat}, m < n -> exists b : α, Sum.inr b in F a m) ∧
          Sum.inl b in F a n) ↔
      b in PFun.fix f a := by
  intro F; refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨n, ⟨_x, h₁⟩, h₂⟩
    have : forall m a', Sum.inr a' in F a m -> b in PFun.fix f a' -> b in PFun.fix f a := by
      intro m a' am ba
      induction m generalizing a' with simp [F] at am
      | zero => rwa [← am]
      | succ m IH =>
        rcases am with ⟨a₂, am₂, fa₂⟩
        exact IH _ am₂ (PFun.mem_fix_iff.2 (Or.inr ⟨_, fa₂, ba⟩))
    cases n <;> simp [F] at h₂
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `obtain`/`specialize`. It is not yet clear whether this is due to defeq abuse
    in Mathlib or a problem in the new canonicalizer; a minimization would help. The original
    proof was:
    ```
    have := h₁ (Nat.lt_succ_self _)
    grind [mem_unique, PFun.mem_fix_iff]
    ```
    -/
    obtain ⟨c, hc⟩ := h₁ (Nat.lt_succ_self _)
    specialize this _ _ hc
    grind [mem_unique, PFun.mem_fix_iff]
  · suffices forall a', b in PFun.fix f a' -> forall k, Sum.inr a' in F a k ->
        exists n, Sum.inl b in F a n ∧ forall m < n, k <= m -> exists a₂, Sum.inr a₂ in F a m by
      rcases this _ h 0 (by simp [F]) with ⟨n, hn₁, hn₂⟩
      exact ⟨_, ⟨⟨_, hn₁⟩, fun {m} mn => hn₂ m mn (Nat.zero_le _)⟩, hn₁⟩
    intro a₁ h₁
    apply @PFun.fixInduction _ _ _ _ _ _ h₁
    intro a₂ h₂ IH k hk
    rcases PFun.mem_fix_iff.1 h₂ with (h₂ | ⟨a₃, am₃, _⟩)
    · refine ⟨k.succ, ?_, fun m mk km => ⟨a₂, ?_⟩⟩
      · simpa [F] using Or.inr ⟨_, hk, h₂⟩
      · rwa [le_antisymm (Nat.le_of_lt_succ mk) km]
    · rcases IH _ am₃ k.succ (by simpa [F] using ⟨_, hk, am₃⟩) with ⟨n, hn₁, hn₂⟩
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer),
      the `clear_value F` was not required here. -/
      clear_value F
      grind

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fix` / 定理 `fix`

English:
theorem fix
  given: {f : α ->. σ oplus α} (hf : Partrec f)
  statement: Partrec (PFun.fix f)
  proof: by
  let F : α -> Nat ->. σ oplus α := fun a n =>
    n.rec (some (Sum.inr a)) fun _ IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
  have hF : Partrec₂ F :=
    Partrec.nat_rec snd (sumInr.comp fst).partrec
      (sumCasesOn_right (snd.comp snd) (snd.comp <| snd.comp fst).to₂ (hf.com

中文:
定理 fix
  条件: {f : α ->. σ oplus α} (hf : Partrec f)
  结论: Partrec (PFun.fix f)
  证明: by
  let F : α -> Nat ->. σ oplus α := fun a n =>
    n.rec (some (Sum.inr a)) fun _ IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
  have hF : Partrec₂ F :=
    Partrec.nat_rec snd (sumInr.comp fst).partrec
      (sumCasesOn_right (snd.comp snd) (snd.comp <| snd.comp fst).to₂ (hf.com

Depends on / 依赖: Computable, Computable.id, IH.bind, Part.map, Part.some, Partrec, Partrec.nat_rec, Sum.casesOn, Sum.inr, casesOn, hF.map, hf.comp, n.rec, nat_rec, partrec, snd.comp, sumCasesOn, sumCasesOn_right, sumInr, sumInr.comp
-/
theorem fix {f : α ->. σ oplus α} (hf : Partrec f) : Partrec (PFun.fix f) := by
  let F : α -> Nat ->. σ oplus α := fun a n =>
    n.rec (some (Sum.inr a)) fun _ IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
  have hF : Partrec₂ F :=
    Partrec.nat_rec snd (sumInr.comp fst).partrec
      (sumCasesOn_right (snd.comp snd) (snd.comp <| snd.comp fst).to₂ (hf.comp snd).to₂).to₂
  let p a n := @Part.map _ Bool (fun s => Sum.casesOn s (fun _ => true) fun _ => false) (F a n)
  have hp : Partrec₂ p :=
    hF.map ((sumCasesOn Computable.id (const true).to₂ (const false).to₂).comp snd).to₂
  exact ((Partrec.rfind hp).bind (hF.bind (sumCasesOn_right snd snd.to₂ none.to₂).to₂).to₂).of_eq
    fun a => ext fun b => by simpa [p] using fix_aux f _ _

end Partrec
