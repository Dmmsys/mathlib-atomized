/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.WSeq.Basic
public import Mathlib.Logic.Relation

/-!
# Relations between and equivalence of weak sequences

This file defines a relation between weak sequences as a relation between their `some` elements,
ignoring computation time (`none` elements). Equivalence is then defined in the obvious way.

## Main definitions

* `Stream'.WSeq.LiftRelO`: Lift a relation to a relation over weak sequences.
* `Stream'.WSeq.LiftRel`: Two sequences are `LiftRel R`-related if their corresponding `some`
  elements are `R`-related.
* `Stream'.WSeq.Equiv`: Two sequences are equivalent if they are `LiftRel (· = ·)`-related.
-/

@[expose] public section

universe u v w

namespace Stream'.WSeq

variable {α : Type u} {β : Type v} {γ : Type w}

open Function

/-- lift a relation to a relation over weak sequences -/
@[simp]
/--
Definition of `LiftRelO` / `LiftRelO` 的定义

English:
definition LiftRelO
  signature: (R : α -> β -> Prop) (C : WSeq α -> WSeq β -> Prop)

中文:
定义 LiftRelO
  签名: (R : α -> β -> 命题) (C : WSeq α -> WSeq β -> 命题)
-/
def LiftRelO (R : α -> β -> Prop) (C : WSeq α -> WSeq β -> Prop) :
    Option (α × WSeq α) -> Option (β × WSeq β) -> Prop
  | none, none => True
  | some (a, s), some (b, t) => R a b ∧ C s t
  | _, _ => False
attribute [nolint simpNF] LiftRelO.eq_3

/--
theorem `LiftRelO.imp` / 定理 `LiftRelO.imp`

English:
theorem LiftRelO.imp
  statement: {R S : α -> β -> Prop} {C D : WSeq α -> WSeq β -> Prop} (H1 : forall a b, R a b -> S a b)

中文:
定理 LiftRelO.imp
  结论: {R S : α -> β -> 命题} {C D : WSeq α -> WSeq β -> 命题} (H1 : 对任意 a b, R a b -> S a b)
-/
theorem LiftRelO.imp {R S : α -> β -> Prop} {C D : WSeq α -> WSeq β -> Prop} (H1 : forall a b, R a b -> S a b)
    (H2 : forall s t, C s t -> D s t) : forall {o p}, LiftRelO R C o p -> LiftRelO S D o p
  | none, none, _ => trivial
  | some (_, _), some (_, _), h => And.imp (H1 _ _) (H2 _ _) h
  | none, some _, h => False.elim h
  | some (_, _), none, h => False.elim h

/--
theorem `LiftRelO.imp_right` / 定理 `LiftRelO.imp_right`

English:
theorem LiftRelO.imp_right
  statement: (R : α -> β -> Prop) {C D : WSeq α -> WSeq β -> Prop}
  proof: LiftRelO.imp (fun _ _ => id) H

中文:
定理 LiftRelO.imp_right
  结论: (R : α -> β -> 命题) {C D : WSeq α -> WSeq β -> 命题}
  证明: LiftRelO.imp (fun _ _ => id) H

Depends on / 依赖: LiftRelO, LiftRelO.imp
-/
theorem LiftRelO.imp_right (R : α -> β -> Prop) {C D : WSeq α -> WSeq β -> Prop}
    (H : forall s t, C s t -> D s t) {o p} : LiftRelO R C o p -> LiftRelO R D o p :=
  LiftRelO.imp (fun _ _ => id) H

/--
theorem `LiftRelO.swap` / 定理 `LiftRelO.swap`

English:
theorem LiftRelO.swap
  given: (R : α -> β -> Prop) (C)
  proof: by
  funext x y
  rcases x with ⟨⟩ | ⟨hx, jx⟩ <;> rcases y with ⟨⟩ | ⟨hy, jy⟩ <;> rfl

中文:
定理 LiftRelO.swap
  条件: (R : α -> β -> 命题) (C)
  证明: by
  funext x y
  rcases x with ⟨⟩ | ⟨hx, jx⟩ <;> rcases y with ⟨⟩ | ⟨hy, jy⟩ <;> rfl
-/
theorem LiftRelO.swap (R : α -> β -> Prop) (C) :
    swap (LiftRelO R C) = LiftRelO (swap R) (swap C) := by
  funext x y
  rcases x with ⟨⟩ | ⟨hx, jx⟩ <;> rcases y with ⟨⟩ | ⟨hy, jy⟩ <;> rfl

/-- Definition of bisimilarity for weak sequences -/
@[simp]
/--
Definition of `BisimO` / `BisimO` 的定义

English:
definition BisimO
  signature: (R : WSeq α -> WSeq α -> Prop)
  body: LiftRelO (· = ·) R

中文:
定义 BisimO
  签名: (R : WSeq α -> WSeq α -> 命题)
  定义体: LiftRelO (· = ·) R

Depends on / 依赖: LiftRelO
-/
def BisimO (R : WSeq α -> WSeq α -> Prop) : Option (α × WSeq α) -> Option (α × WSeq α) -> Prop :=
  LiftRelO (· = ·) R

/--
theorem `BisimO.imp` / 定理 `BisimO.imp`

English:
theorem BisimO.imp
  given: {R S : WSeq α -> WSeq α -> Prop} (H : forall s t, R s t -> S s t) {o p}
  proof: LiftRelO.imp_right _ H

中文:
定理 BisimO.imp
  条件: {R S : WSeq α -> WSeq α -> 命题} (H : 对任意 s t, R s t -> S s t) {o p}
  证明: LiftRelO.imp_right _ H

Depends on / 依赖: LiftRelO, LiftRelO.imp_right, imp_right
-/
theorem BisimO.imp {R S : WSeq α -> WSeq α -> Prop} (H : forall s t, R s t -> S s t) {o p} :
    BisimO R o p -> BisimO S o p :=
  LiftRelO.imp_right _ H

/--
Definition of `LiftRel` / `LiftRel` 的定义

English:
definition LiftRel
  signature: (R : α -> β -> Prop) (s : WSeq α) (t : WSeq β)
  body: exists C : WSeq α -> WSeq β -> Prop,
    C s t ∧ forall {s t}, C s t -> Computation.LiftRel (LiftRelO R C) (destruct s) (destruct t)

中文:
定义 LiftRel
  签名: (R : α -> β -> 命题) (s : WSeq α) (t : WSeq β)
  定义体: exists C : WSeq α -> WSeq β -> Prop,
    C s t ∧ forall {s t}, C s t -> Computation.LiftRel (LiftRelO R C) (destruct s) (destruct t)

Depends on / 依赖: Computation, Computation.LiftRel, LiftRel, LiftRelO, destruct
-/
def LiftRel (R : α -> β -> Prop) (s : WSeq α) (t : WSeq β) : Prop :=
  exists C : WSeq α -> WSeq β -> Prop,
    C s t ∧ forall {s t}, C s t -> Computation.LiftRel (LiftRelO R C) (destruct s) (destruct t)

/--
theorem `liftRel_destruct` / 定理 `liftRel_destruct`

English:
theorem liftRel_destruct
  given: {R : α -> β -> Prop} {s : WSeq α} {t : WSeq β}

中文:
定理 liftRel_destruct
  条件: {R : α -> β -> 命题} {s : WSeq α} {t : WSeq β}
-/
theorem liftRel_destruct {R : α -> β -> Prop} {s : WSeq α} {t : WSeq β} :
    LiftRel R s t -> Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t)
  | ⟨R, h1, h2⟩ => by
    refine Computation.LiftRel.imp ?_ _ _ (h2 h1)
    apply LiftRelO.imp_right
    exact fun s' t' h' => ⟨R, h', @h2⟩

/--
theorem `liftRel_destruct_iff` / 定理 `liftRel_destruct_iff`

English:
theorem liftRel_destruct_iff
  given: {R : α -> β -> Prop} {s : WSeq α} {t : WSeq β}
  proof: ⟨liftRel_destruct, fun h =>
    ⟨fun s t =>
      LiftRel R s t ∨ Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t),
      Or.inr h, fun {s t} h => by
      have h : Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t) := by
        obtain h | h := h
        · 

中文:
定理 liftRel_destruct_iff
  条件: {R : α -> β -> 命题} {s : WSeq α} {t : WSeq β}
  证明: ⟨liftRel_destruct, fun h =>
    ⟨fun s t =>
      LiftRel R s t ∨ Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t),
      Or.inr h, fun {s t} h => by
      have h : Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t) := by
        obtain h | h := h
        · 

Depends on / 依赖: Computation, Computation.LiftRel, Computation.LiftRel.imp, LiftRel, LiftRelO, LiftRelO.imp_right, Or.inl, Or.inr, destruct, imp_right, liftRel_destruct
-/
theorem liftRel_destruct_iff {R : α -> β -> Prop} {s : WSeq α} {t : WSeq β} :
    LiftRel R s t ↔ Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t) :=
  ⟨liftRel_destruct, fun h =>
    ⟨fun s t =>
      LiftRel R s t ∨ Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t),
      Or.inr h, fun {s t} h => by
      have h : Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t) := by
        obtain h | h := h
        · exact liftRel_destruct h
        · assumption
      apply Computation.LiftRel.imp _ _ _ h
      apply LiftRelO.imp_right
      intro s t
      apply Or.inl⟩⟩

/--
theorem `LiftRel.swap_lem` / 定理 `LiftRel.swap_lem`

English:
theorem LiftRel.swap_lem
  given: {R : α -> β -> Prop} {s1 s2} (h : LiftRel R s1 s2)
  proof: by
  refine ⟨swap (LiftRel R), h, fun {s t} (h : LiftRel R t s) => ?_⟩
  rw [← LiftRelO.swap]; rw [Computation.LiftRel.swap]
  apply liftRel_destruct h

中文:
定理 LiftRel.swap_lem
  条件: {R : α -> β -> 命题} {s1 s2} (h : LiftRel R s1 s2)
  证明: by
  refine ⟨swap (LiftRel R), h, fun {s t} (h : LiftRel R t s) => ?_⟩
  rw [← LiftRelO.swap]; rw [Computation.LiftRel.swap]
  apply liftRel_destruct h

Depends on / 依赖: Computation, Computation.LiftRel.swap, LiftRel, LiftRelO, LiftRelO.swap, liftRel_destruct
-/
theorem LiftRel.swap_lem {R : α -> β -> Prop} {s1 s2} (h : LiftRel R s1 s2) :
    LiftRel (swap R) s2 s1 := by
  refine ⟨swap (LiftRel R), h, fun {s t} (h : LiftRel R t s) => ?_⟩
  rw [← LiftRelO.swap]; rw [Computation.LiftRel.swap]
  apply liftRel_destruct h

/--
theorem `LiftRel.swap` / 定理 `LiftRel.swap`

English:
theorem LiftRel.swap
  given: (R : α -> β -> Prop)
  statement: swap (LiftRel R) = LiftRel (swap R)
  proof: funext fun _ => funext fun _ => propext ⟨LiftRel.swap_lem, LiftRel.swap_lem⟩

中文:
定理 LiftRel.swap
  条件: (R : α -> β -> 命题)
  结论: swap (LiftRel R) = LiftRel (swap R)
  证明: funext fun _ => funext fun _ => propext ⟨LiftRel.swap_lem, LiftRel.swap_lem⟩

Depends on / 依赖: isFreeGroup, ofFreeGroup
-/
theorem LiftRel.swap (R : α -> β -> Prop) : swap (LiftRel R) = LiftRel (swap R) :=
  funext fun _ => funext fun _ => propext ⟨LiftRel.swap_lem, LiftRel.swap_lem⟩

/--
Instance `LiftRelO.refl` / 实例 `LiftRelO.refl`

English:
instance LiftRelO.refl
  signature: (R : α -> α -> Prop) [Std.Refl R]
  body: by
    rcases a with - | a
    · simp
    · cases a
      simp only [LiftRelO, and_true]
      apply refl_of R

中文:
实例 LiftRelO.refl
  签名: (R : α -> α -> 命题) [Std.Refl R]
  定义体: by
    rcases a with - | a
    · simp
    · cases a
      simp only [LiftRelO, and_true]
      apply refl_of R

Depends on / 依赖: LiftRelO, and_true, refl_of
-/
instance LiftRelO.refl (R : α -> α -> Prop) [Std.Refl R] : Std.Refl LiftRelO R (· = ·) where
  refl a := by
    rcases a with - | a
    · simp
    · cases a
      simp only [LiftRelO, and_true]
      apply refl_of R

/--
Instance `LiftRel.refl` / 实例 `LiftRel.refl`

English:
instance LiftRel.refl
  signature: (R : α -> α -> Prop) [Std.Refl R]
  body: by
    refine ⟨(· = ·), rfl, fun {s t} (h : s = t) => ?_⟩
    rw [← h]
.refl apply Computation.LiftRel.refl _

中文:
实例 LiftRel.refl
  签名: (R : α -> α -> 命题) [Std.Refl R]
  定义体: by
    refine ⟨(· = ·), rfl, fun {s t} (h : s = t) => ?_⟩
    rw [← h]
.refl apply Computation.LiftRel.refl _
-/
instance LiftRel.refl (R : α -> α -> Prop) [Std.Refl R] : Std.Refl (LiftRel R) where
  refl s := by
    refine ⟨(· = ·), rfl, fun {s t} (h : s = t) => ?_⟩
    rw [← h]
.refl apply Computation.LiftRel.refl _

/--
Instance `LiftRel.symm` / 实例 `LiftRel.symm`

English:
instance LiftRel.symm
  signature: (R : α -> α -> Prop) [Std.Symm R]
  body: by rwa [LiftRel.swap, Std.Symm.swap_eq] at h

中文:
实例 LiftRel.symm
  签名: (R : α -> α -> 命题) [Std.Symm R]
  定义体: by rwa [LiftRel.swap, Std.Symm.swap_eq] at h
-/
instance LiftRel.symm (R : α -> α -> Prop) [Std.Symm R] : Std.Symm (LiftRel R) where
  symm s1 s2 (h : Function.swap (LiftRel R) s2 s1) := by rwa [LiftRel.swap, Std.Symm.swap_eq] at h

/--
Instance `LiftRel.trans` / 实例 `LiftRel.trans`

English:
instance LiftRel.trans
  signature: (R : α -> α -> Prop) [IsTrans α R]
  body: by
  refine ⟨fun s t u h1 h2 => ?_⟩
  refine ⟨fun s u => exists t, LiftRel R s t ∧ LiftRel R t u, ⟨t, h1, h2⟩, fun {s u} h => ?_⟩
  rcases h with ⟨t, h1, h2⟩
  have h1 := liftRel_destruct h1
  have h2 := liftRel_destruct h2
  refine
    Computation.liftRel_def.2
      ⟨(Computation.terminates_of_lif

中文:
实例 LiftRel.trans
  签名: (R : α -> α -> 命题) [是Trans α R]
  定义体: by
  refine ⟨fun s t u h1 h2 => ?_⟩
  refine ⟨fun s u => exists t, LiftRel R s t ∧ LiftRel R t u, ⟨t, h1, h2⟩, fun {s u} h => ?_⟩
  rcases h with ⟨t, h1, h2⟩
  have h1 := liftRel_destruct h1
  have h2 := liftRel_destruct h2
  refine
    Computation.liftRel_def.2
      ⟨(Computation.terminates_of_lif
-/
instance LiftRel.trans (R : α -> α -> Prop) [IsTrans α R] : IsTrans _ (LiftRel R) := by
  refine ⟨fun s t u h1 h2 => ?_⟩
  refine ⟨fun s u => exists t, LiftRel R s t ∧ LiftRel R t u, ⟨t, h1, h2⟩, fun {s u} h => ?_⟩
  rcases h with ⟨t, h1, h2⟩
  have h1 := liftRel_destruct h1
  have h2 := liftRel_destruct h2
  refine
    Computation.liftRel_def.2
      ⟨(Computation.terminates_of_liftRel h1).trans (Computation.terminates_of_liftRel h2),
        fun {a c} ha hc => ?_⟩
  rcases h1.left ha with ⟨b, hb, t1⟩
  have t2 := Computation.rel_of_liftRel h2 hb hc
  obtain - | a := a <;> obtain - | c := c
  · trivial
  · cases b
    · cases t2
    · cases t1
  · cases a
    rcases b with - | b
    · cases t1
    · cases b
      cases t2
  · obtain ⟨a, s⟩ := a
    rcases b with - | b
    · cases t1
    obtain ⟨b, t⟩ := b
    obtain ⟨c, u⟩ := c
    obtain ⟨ab, st⟩ := t1
    obtain ⟨bc, tu⟩ := t2
    exact ⟨trans_of R ab bc, t, st, tu⟩

/--
theorem `LiftRel.equiv` / 定理 `LiftRel.equiv`

English:
theorem LiftRel.equiv
  given: (R : α -> α -> Prop) (H : Equivalence R)
  statement: Equivalence (LiftRel R) where
  proof: @LiftRel.refl α R H.stdRefl
.symm _ _ symm := @LiftRel.symm α R H.stdSymm
.trans _ _ _ trans := @LiftRel.trans α R H.isTrans

中文:
定理 LiftRel.equiv
  条件: (R : α -> α -> 命题) (H : 等价 R)
  结论: 等价 (LiftRel R) where
  证明: @LiftRel.refl α R H.stdRefl
.symm _ _ symm := @LiftRel.symm α R H.stdSymm
.trans _ _ _ trans := @LiftRel.trans α R H.isTrans
-/
theorem LiftRel.equiv (R : α -> α -> Prop) (H : Equivalence R) : Equivalence (LiftRel R) where
.refl refl := @LiftRel.refl α R H.stdRefl
.symm _ _ symm := @LiftRel.symm α R H.stdSymm
.trans _ _ _ trans := @LiftRel.trans α R H.isTrans

/--
Definition of `Equiv` / `Equiv` 的定义

English:
definition Equiv
  signature: : WSeq α -> WSeq α -> Prop
  body: LiftRel Eq

@[inherit_doc] infixl:50 " ~ʷ " => Equiv

@[refl]

中文:
定义 等价
  签名: : WSeq α -> WSeq α -> 命题
  定义体: LiftRel Eq

@[inherit_doc] infixl:50 " ~ʷ " => Equiv

@[refl]

Depends on / 依赖: LiftRel
-/
def Equiv : WSeq α -> WSeq α -> Prop :=
  LiftRel Eq

@[inherit_doc] infixl:50 " ~ʷ " => Equiv

@[refl]
/--
theorem `Equiv.refl` / 定理 `Equiv.refl`

English:
theorem Equiv.refl
  statement: forall s : WSeq α, s ~ʷ s
  proof: .refl LiftRel.refl Eq

@[symm]

中文:
定理 等价.refl
  结论: 对任意 s : WSeq α, s ~ʷ s
  证明: .refl LiftRel.refl Eq

@[symm]
-/
theorem Equiv.refl : forall s : WSeq α, s ~ʷ s :=
.refl LiftRel.refl Eq

@[symm]
/--
theorem `Equiv.symm` / 定理 `Equiv.symm`

English:
theorem Equiv.symm
  statement: forall {s t : WSeq α}, s ~ʷ t -> t ~ʷ s
  proof: .symm _ _ LiftRel.symm Eq

@[trans]

中文:
定理 等价.symm
  结论: 对任意 {s t : WSeq α}, s ~ʷ t -> t ~ʷ s
  证明: .symm _ _ LiftRel.symm Eq

@[trans]
-/
theorem Equiv.symm : forall {s t : WSeq α}, s ~ʷ t -> t ~ʷ s :=
.symm _ _ LiftRel.symm Eq

@[trans]
/--
theorem `Equiv.trans` / 定理 `Equiv.trans`

English:
theorem Equiv.trans
  statement: forall {s t u : WSeq α}, s ~ʷ t -> t ~ʷ u -> s ~ʷ u
  proof: .trans _ _ _ LiftRel.trans Eq

中文:
定理 等价.trans
  结论: 对任意 {s t u : WSeq α}, s ~ʷ t -> t ~ʷ u -> s ~ʷ u
  证明: .trans _ _ _ LiftRel.trans Eq
-/
theorem Equiv.trans : forall {s t u : WSeq α}, s ~ʷ t -> t ~ʷ u -> s ~ʷ u :=
.trans _ _ _ LiftRel.trans Eq

/--
theorem `Equiv.equivalence` / 定理 `Equiv.equivalence`

English:
theorem Equiv.equivalence
  statement: Equivalence (@Equiv α)
  proof: ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩

中文:
定理 等价.equivalence
  结论: 等价 (@等价 α)
  证明: ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩
-/
theorem Equiv.equivalence : Equivalence (@Equiv α) :=
  ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩

/--
theorem `destruct_congr` / 定理 `destruct_congr`

English:
theorem destruct_congr
  given: {s t : WSeq α}
  proof: liftRel_destruct

中文:
定理 destruct_congr
  条件: {s t : WSeq α}
  证明: liftRel_destruct

Depends on / 依赖: liftRel_destruct
-/
theorem destruct_congr {s t : WSeq α} :
    s ~ʷ t -> Computation.LiftRel (BisimO (· ~ʷ ·)) (destruct s) (destruct t) :=
  liftRel_destruct

/--
theorem `destruct_congr_iff` / 定理 `destruct_congr_iff`

English:
theorem destruct_congr_iff
  given: {s t : WSeq α}
  proof: liftRel_destruct_iff

中文:
定理 destruct_congr_iff
  条件: {s t : WSeq α}
  证明: liftRel_destruct_iff

Depends on / 依赖: liftRel_destruct_iff
-/
theorem destruct_congr_iff {s t : WSeq α} :
    s ~ʷ t ↔ Computation.LiftRel (BisimO (· ~ʷ ·)) (destruct s) (destruct t) :=
  liftRel_destruct_iff

open Computation

/--
theorem `liftRel_dropn_destruct` / 定理 `liftRel_dropn_destruct`

English:
theorem liftRel_dropn_destruct
  given: {R : α -> β -> Prop} {s t} (H : LiftRel R s t)

中文:
定理 liftRel_dropn_destruct
  条件: {R : α -> β -> 命题} {s t} (H : LiftRel R s t)
-/
theorem liftRel_dropn_destruct {R : α -> β -> Prop} {s t} (H : LiftRel R s t) :
    forall n, Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct (drop s n)) (destruct (drop t n))
  | 0 => liftRel_destruct H
  | n + 1 => by
    simp only [drop, destruct_tail]
    apply liftRel_bind
    · apply liftRel_dropn_destruct H n
    exact fun {a b} o =>
      match a, b, o with
      | none, none, _ => by simp
      | some (a, s), some (b, t), ⟨_, h2⟩ => by simpa [tail.aux] using liftRel_destruct h2

/--
theorem `exists_of_liftRel_left` / 定理 `exists_of_liftRel_left`

English:
theorem exists_of_liftRel_left
  given: {R : α -> β -> Prop} {s t} (H : LiftRel R s t) {a} (h : a in s)
  proof: by
  let ⟨n, h⟩ := exists_get?_of_mem h
  let ⟨some (_, s'), sd, rfl⟩ := Computation.exists_of_mem_map h
  let ⟨some (b, t'), td, ⟨ab, _⟩⟩ := (liftRel_dropn_destruct H n).left sd
  exact ⟨b, get?_mem (Computation.mem_map (Prod.fst.{v, v} <$> ·) td), ab⟩

中文:
定理 存在_of_liftRel_left
  条件: {R : α -> β -> 命题} {s t} (H : LiftRel R s t) {a} (h : a in s)
  证明: by
  let ⟨n, h⟩ := exists_get?_of_mem h
  let ⟨some (_, s'), sd, rfl⟩ := Computation.exists_of_mem_map h
  let ⟨some (b, t'), td, ⟨ab, _⟩⟩ := (liftRel_dropn_destruct H n).left sd
  exact ⟨b, get?_mem (Computation.mem_map (Prod.fst.{v, v} <$> ·) td), ab⟩

Depends on / 依赖: Computation, Computation.exists_of_mem_map, Computation.mem_map, Prod.fst, _mem, _of_mem, exists_get, exists_of_mem_map, liftRel_dropn_destruct, mem_map
-/
theorem exists_of_liftRel_left {R : α -> β -> Prop} {s t} (H : LiftRel R s t) {a} (h : a in s) :
    exists b, b in t ∧ R a b := by
  let ⟨n, h⟩ := exists_get?_of_mem h
  let ⟨some (_, s'), sd, rfl⟩ := Computation.exists_of_mem_map h
  let ⟨some (b, t'), td, ⟨ab, _⟩⟩ := (liftRel_dropn_destruct H n).left sd
  exact ⟨b, get?_mem (Computation.mem_map (Prod.fst.{v, v} <$> ·) td), ab⟩

/--
theorem `exists_of_liftRel_right` / 定理 `exists_of_liftRel_right`

English:
theorem exists_of_liftRel_right
  given: {R : α -> β -> Prop} {s t} (H : LiftRel R s t) {b} (h : b in t)
  proof: by rw [← LiftRel.swap] at H; exact exists_of_liftRel_left H h

@[simp]

中文:
定理 存在_of_liftRel_right
  条件: {R : α -> β -> 命题} {s t} (H : LiftRel R s t) {b} (h : b in t)
  证明: by rw [← LiftRel.swap] at H; exact exists_of_liftRel_left H h

@[simp]

Depends on / 依赖: LiftRel, LiftRel.swap, exists_of_liftRel_left
-/
theorem exists_of_liftRel_right {R : α -> β -> Prop} {s t} (H : LiftRel R s t) {b} (h : b in t) :
    exists a, a in s ∧ R a b := by rw [← LiftRel.swap] at H; exact exists_of_liftRel_left H h

@[simp]
/--
theorem `liftRel_nil` / 定理 `liftRel_nil`

English:
theorem liftRel_nil
  given: (R : α -> β -> Prop)
  statement: LiftRel R nil nil
  proof: by
  simp [liftRel_destruct_iff]

@[simp]

中文:
定理 liftRel_nil
  条件: (R : α -> β -> 命题)
  结论: LiftRel R nil nil
  证明: by
  simp [liftRel_destruct_iff]

@[simp]

Depends on / 依赖: liftRel_destruct_iff
-/
theorem liftRel_nil (R : α -> β -> Prop) : LiftRel R nil nil := by
  simp [liftRel_destruct_iff]

@[simp]
/--
theorem `liftRel_cons` / 定理 `liftRel_cons`

English:
theorem liftRel_cons
  given: (R : α -> β -> Prop) (a b s t)
  proof: by
  simp [liftRel_destruct_iff]

@[simp]

中文:
定理 liftRel_cons
  条件: (R : α -> β -> 命题) (a b s t)
  证明: by
  simp [liftRel_destruct_iff]

@[simp]

Depends on / 依赖: liftRel_destruct_iff
-/
theorem liftRel_cons (R : α -> β -> Prop) (a b s t) :
    LiftRel R (cons a s) (cons b t) ↔ R a b ∧ LiftRel R s t := by
  simp [liftRel_destruct_iff]

@[simp]
/--
theorem `liftRel_think_left` / 定理 `liftRel_think_left`

English:
theorem liftRel_think_left
  given: (R : α -> β -> Prop) (s t)
  statement: LiftRel R (think s) t ↔ LiftRel R s t
  proof: by
  rw [liftRel_destruct_iff]; rw [liftRel_destruct_iff]; simp

@[simp]

中文:
定理 liftRel_think_left
  条件: (R : α -> β -> 命题) (s t)
  结论: LiftRel R (think s) t ↔ LiftRel R s t
  证明: by
  rw [liftRel_destruct_iff]; rw [liftRel_destruct_iff]; simp

@[simp]

Depends on / 依赖: liftRel_destruct_iff
-/
theorem liftRel_think_left (R : α -> β -> Prop) (s t) : LiftRel R (think s) t ↔ LiftRel R s t := by
  rw [liftRel_destruct_iff]; rw [liftRel_destruct_iff]; simp

@[simp]
/--
theorem `liftRel_think_right` / 定理 `liftRel_think_right`

English:
theorem liftRel_think_right
  given: (R : α -> β -> Prop) (s t)
  statement: LiftRel R s (think t) ↔ LiftRel R s t
  proof: by
  rw [liftRel_destruct_iff]; rw [liftRel_destruct_iff]; simp

中文:
定理 liftRel_think_right
  条件: (R : α -> β -> 命题) (s t)
  结论: LiftRel R s (think t) ↔ LiftRel R s t
  证明: by
  rw [liftRel_destruct_iff]; rw [liftRel_destruct_iff]; simp

Depends on / 依赖: liftRel_destruct_iff
-/
theorem liftRel_think_right (R : α -> β -> Prop) (s t) : LiftRel R s (think t) ↔ LiftRel R s t := by
  rw [liftRel_destruct_iff]; rw [liftRel_destruct_iff]; simp

/--
theorem `cons_congr` / 定理 `cons_congr`

English:
theorem cons_congr
  given: {s t : WSeq α} (a : α) (h : s ~ʷ t)
  statement: cons a s ~ʷ cons a t
  proof: by
  unfold Equiv; simpa using! h

中文:
定理 cons_congr
  条件: {s t : WSeq α} (a : α) (h : s ~ʷ t)
  结论: cons a s ~ʷ cons a t
  证明: by
  unfold Equiv; simpa using! h
-/
theorem cons_congr {s t : WSeq α} (a : α) (h : s ~ʷ t) : cons a s ~ʷ cons a t := by
  unfold Equiv; simpa using! h

/--
theorem `think_equiv` / 定理 `think_equiv`

English:
theorem think_equiv
  given: (s : WSeq α)
  statement: think s ~ʷ s
  proof: by unfold Equiv; simpa using! Equiv.refl _

中文:
定理 think_equiv
  条件: (s : WSeq α)
  结论: think s ~ʷ s
  证明: by unfold Equiv; simpa using! Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
theorem think_equiv (s : WSeq α) : think s ~ʷ s := by unfold Equiv; simpa using! Equiv.refl _

/--
theorem `think_congr` / 定理 `think_congr`

English:
theorem think_congr
  given: {s t : WSeq α} (h : s ~ʷ t)
  statement: think s ~ʷ think t
  proof: by
  unfold Equiv; simpa using! h

中文:
定理 think_congr
  条件: {s t : WSeq α} (h : s ~ʷ t)
  结论: think s ~ʷ think t
  证明: by
  unfold Equiv; simpa using! h
-/
theorem think_congr {s t : WSeq α} (h : s ~ʷ t) : think s ~ʷ think t := by
  unfold Equiv; simpa using! h

/--
theorem `head_congr` / 定理 `head_congr`

English:
theorem head_congr
  statement: forall {s t : WSeq α}, s ~ʷ t -> head s ~ head t
  proof: by
  suffices forall {s t : WSeq α}, s ~ʷ t -> forall {o}, o in head s -> o in head t from fun s t h o =>
    ⟨this h, this h.symm⟩
  intro s t h o ho
  rcases @Computation.exists_of_mem_map _ _ _ _ (destruct s) ho with ⟨ds, dsm, dse⟩
  rw [← dse]
  obtain ⟨l, r⟩ := destruct_congr h
  rcases l dsm w

中文:
定理 head_congr
  结论: 对任意 {s t : WSeq α}, s ~ʷ t -> head s ~ head t
  证明: by
  suffices forall {s t : WSeq α}, s ~ʷ t -> forall {o}, o in head s -> o in head t from fun s t h o =>
    ⟨this h, this h.symm⟩
  intro s t h o ho
  rcases @Computation.exists_of_mem_map _ _ _ _ (destruct s) ho with ⟨ds, dsm, dse⟩
  rw [← dse]
  obtain ⟨l, r⟩ := destruct_congr h
  rcases l dsm w

Depends on / 依赖: Computation, Computation.exists_of_mem_map, Computation.me, Computation.mem_map, destruct, destruct_congr, dst.left, exists_of_mem_map, h.symm, mem_map
-/
theorem head_congr : forall {s t : WSeq α}, s ~ʷ t -> head s ~ head t := by
  suffices forall {s t : WSeq α}, s ~ʷ t -> forall {o}, o in head s -> o in head t from fun s t h o =>
    ⟨this h, this h.symm⟩
  intro s t h o ho
  rcases @Computation.exists_of_mem_map _ _ _ _ (destruct s) ho with ⟨ds, dsm, dse⟩
  rw [← dse]
  obtain ⟨l, r⟩ := destruct_congr h
  rcases l dsm with ⟨dt, dtm, dst⟩
  rcases ds with - | a <;> rcases dt with - | b
  · apply Computation.mem_map _ dtm
  · cases b
    cases dst
  · cases a
    cases dst
  · obtain ⟨a, s'⟩ := a
    obtain ⟨b, t'⟩ := b
    rw [dst.left]
    exact @Computation.mem_map _ _ (@Functor.map _ _ (α × WSeq α) _ Prod.fst)
      (some (b, t')) (destruct t) dtm

/--
theorem `flatten_equiv` / 定理 `flatten_equiv`

English:
theorem flatten_equiv
  given: {c : Computation (WSeq α)} {s} (h : s in c)
  statement: flatten c ~ʷ s
  proof: by
  apply Computation.memRecOn h
  · simp [Equiv.refl]
  · intro s'
    apply Equiv.trans
    simp [think_equiv]

中文:
定理 flatten_equiv
  条件: {c : Computation (WSeq α)} {s} (h : s in c)
  结论: flatten c ~ʷ s
  证明: by
  apply Computation.memRecOn h
  · simp [Equiv.refl]
  · intro s'
    apply Equiv.trans
    simp [think_equiv]

Depends on / 依赖: Computation, Computation.memRecOn, Equiv.refl, Equiv.trans, memRecOn, think_equiv
-/
theorem flatten_equiv {c : Computation (WSeq α)} {s} (h : s in c) : flatten c ~ʷ s := by
  apply Computation.memRecOn h
  · simp [Equiv.refl]
  · intro s'
    apply Equiv.trans
    simp [think_equiv]

/--
theorem `liftRel_flatten` / 定理 `liftRel_flatten`

English:
theorem liftRel_flatten
  statement: {R : α -> β -> Prop} {c1 : Computation (WSeq α)} {c2 : Computation (WSeq β)}
  proof: let S s t := exists c1 c2, s = flatten c1 ∧ t = flatten c2 ∧ Computation.LiftRel (LiftRel R) c1 c2
  ⟨S, ⟨c1, c2, rfl, rfl, h⟩, fun {s t} h =>
    match s, t, h with
    | _, _, ⟨c1, c2, rfl, rfl, h⟩ => by
      simp only [destruct_flatten]; apply liftRel_bind _ _ h
      intro a b ab; apply Computa

中文:
定理 liftRel_flatten
  结论: {R : α -> β -> 命题} {c1 : Computation (WSeq α)} {c2 : Computation (WSeq β)}
  证明: let S s t := exists c1 c2, s = flatten c1 ∧ t = flatten c2 ∧ Computation.LiftRel (LiftRel R) c1 c2
  ⟨S, ⟨c1, c2, rfl, rfl, h⟩, fun {s t} h =>
    match s, t, h with
    | _, _, ⟨c1, c2, rfl, rfl, h⟩ => by
      simp only [destruct_flatten]; apply liftRel_bind _ _ h
      intro a b ab; apply Computa

Depends on / 依赖: Computation, Computation.LiftRel, Computation.LiftRel.imp, Computation.pure, LiftRel, LiftRelO, LiftRelO.imp_right, destruct_flatten, flatten, imp_right, liftRel_bind, liftRel_destruct
-/
theorem liftRel_flatten {R : α -> β -> Prop} {c1 : Computation (WSeq α)} {c2 : Computation (WSeq β)}
    (h : c1.LiftRel (LiftRel R) c2) : LiftRel R (flatten c1) (flatten c2) :=
  let S s t := exists c1 c2, s = flatten c1 ∧ t = flatten c2 ∧ Computation.LiftRel (LiftRel R) c1 c2
  ⟨S, ⟨c1, c2, rfl, rfl, h⟩, fun {s t} h =>
    match s, t, h with
    | _, _, ⟨c1, c2, rfl, rfl, h⟩ => by
      simp only [destruct_flatten]; apply liftRel_bind _ _ h
      intro a b ab; apply Computation.LiftRel.imp _ _ _ (liftRel_destruct ab)
      intro a b; apply LiftRelO.imp_right
      intro s t h; refine ⟨Computation.pure s, Computation.pure t, ?_, ?_, ?_⟩ <;> simp [h]⟩

/--
theorem `flatten_congr` / 定理 `flatten_congr`

English:
theorem flatten_congr
  given: {c1 c2 : Computation (WSeq α)}
  proof: liftRel_flatten

中文:
定理 flatten_congr
  条件: {c1 c2 : Computation (WSeq α)}
  证明: liftRel_flatten

Depends on / 依赖: liftRel_flatten
-/
theorem flatten_congr {c1 c2 : Computation (WSeq α)} :
    Computation.LiftRel Equiv c1 c2 -> flatten c1 ~ʷ flatten c2 :=
  liftRel_flatten

/--
theorem `tail_congr` / 定理 `tail_congr`

English:
theorem tail_congr
  given: {s t : WSeq α} (h : s ~ʷ t)
  statement: tail s ~ʷ tail t
  proof: by
  apply flatten_congr
  dsimp only [(· <$> ·)]; rw [← Computation.bind_pure, ← Computation.bind_pure]
  apply liftRel_bind _ _ (destruct_congr h)
  intro a b h; simp only [comp_apply, liftRel_pure]
  rcases a with - | a <;> rcases b with - | b
  · trivial
  · cases h
  · cases a
    cases h
  · o

中文:
定理 tail_congr
  条件: {s t : WSeq α} (h : s ~ʷ t)
  结论: tail s ~ʷ tail t
  证明: by
  apply flatten_congr
  dsimp only [(· <$> ·)]; rw [← Computation.bind_pure, ← Computation.bind_pure]
  apply liftRel_bind _ _ (destruct_congr h)
  intro a b h; simp only [comp_apply, liftRel_pure]
  rcases a with - | a <;> rcases b with - | b
  · trivial
  · cases h
  · cases a
    cases h
  · o

Depends on / 依赖: Computation, Computation.bind_pure, bind_pure, comp_apply, destruct_congr, flatten_congr, h.right, liftRel_bind, liftRel_pure
-/
theorem tail_congr {s t : WSeq α} (h : s ~ʷ t) : tail s ~ʷ tail t := by
  apply flatten_congr
  dsimp only [(· <$> ·)]; rw [← Computation.bind_pure, ← Computation.bind_pure]
  apply liftRel_bind _ _ (destruct_congr h)
  intro a b h; simp only [comp_apply, liftRel_pure]
  rcases a with - | a <;> rcases b with - | b
  · trivial
  · cases h
  · cases a
    cases h
  · obtain ⟨a, s'⟩ := a
    obtain ⟨b, t'⟩ := b
    exact h.right

/--
theorem `dropn_congr` / 定理 `dropn_congr`

English:
theorem dropn_congr
  given: {s t : WSeq α} (h : s ~ʷ t) (n)
  statement: drop s n ~ʷ drop t n
  proof: by
  induction n <;> simp [*, tail_congr, drop]

中文:
定理 dropn_congr
  条件: {s t : WSeq α} (h : s ~ʷ t) (n)
  结论: drop s n ~ʷ drop t n
  证明: by
  induction n <;> simp [*, tail_congr, drop]

Depends on / 依赖: tail_congr
-/
theorem dropn_congr {s t : WSeq α} (h : s ~ʷ t) (n) : drop s n ~ʷ drop t n := by
  induction n <;> simp [*, tail_congr, drop]

/--
theorem `get?_congr` / 定理 `get?_congr`

English:
theorem get?_congr
  given: {s t : WSeq α} (h : s ~ʷ t) (n)
  statement: get? s n ~ get? t n
  proof: head_congr (dropn_congr h _)

中文:
定理 get?_congr
  条件: {s t : WSeq α} (h : s ~ʷ t) (n)
  结论: get? s n ~ get? t n
  证明: head_congr (dropn_congr h _)
-/
theorem get?_congr {s t : WSeq α} (h : s ~ʷ t) (n) : get? s n ~ get? t n :=
  head_congr (dropn_congr h _)

/--
theorem `mem_congr` / 定理 `mem_congr`

English:
theorem mem_congr
  given: {s t : WSeq α} (h : s ~ʷ t) (a)
  statement: a in s ↔ a in t
  proof: suffices forall {s t : WSeq α}, s ~ʷ t -> a in s -> a in t from ⟨this h, this h.symm⟩
  fun {_ _} h as =>
  let ⟨_, hn⟩ := exists_get?_of_mem as
  get?_mem ((get?_congr h _ _).1 hn)

中文:
定理 mem_congr
  条件: {s t : WSeq α} (h : s ~ʷ t) (a)
  结论: a in s ↔ a in t
  证明: suffices forall {s t : WSeq α}, s ~ʷ t -> a in s -> a in t from ⟨this h, this h.symm⟩
  fun {_ _} h as =>
  let ⟨_, hn⟩ := exists_get?_of_mem as
  get?_mem ((get?_congr h _ _).1 hn)

Depends on / 依赖: _congr, _mem, _of_mem, exists_get, h.symm
-/
theorem mem_congr {s t : WSeq α} (h : s ~ʷ t) (a) : a in s ↔ a in t :=
  suffices forall {s t : WSeq α}, s ~ʷ t -> a in s -> a in t from ⟨this h, this h.symm⟩
  fun {_ _} h as =>
  let ⟨_, hn⟩ := exists_get?_of_mem as
  get?_mem ((get?_congr h _ _).1 hn)

/--
theorem `Equiv.ext` / 定理 `Equiv.ext`

English:
theorem Equiv.ext
  given: {s t : WSeq α} (h : forall n, get? s n ~ get? t n)
  statement: s ~ʷ t
  proof: ⟨fun s t => forall n, get? s n ~ get? t n, h, fun {s t} h => by
    refine liftRel_def.2 ⟨?_, ?_⟩
    · rw [← head_terminates_iff, ← head_terminates_iff]
      exact terminates_congr (h 0)
    · intro a b ma mb
      rcases a with - | a <;> rcases b with - | b
      · trivial
      · injection mem_u

中文:
定理 等价.ext
  条件: {s t : WSeq α} (h : 对任意 n, get? s n ~ get? t n)
  结论: s ~ʷ t
  证明: ⟨fun s t => forall n, get? s n ~ get? t n, h, fun {s t} h => by
    refine liftRel_def.2 ⟨?_, ?_⟩
    · rw [← head_terminates_iff, ← head_terminates_iff]
      exact terminates_congr (h 0)
    · intro a b ma mb
      rcases a with - | a <;> rcases b with - | b
      · trivial
      · injection mem_u

Depends on / 依赖: Computation, Computation.mem_map, head_terminates_iff, injection, liftRel_def, mem_map, mem_unique, terminates_congr
-/
theorem Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) : s ~ʷ t :=
  ⟨fun s t => forall n, get? s n ~ get? t n, h, fun {s t} h => by
    refine liftRel_def.2 ⟨?_, ?_⟩
    · rw [← head_terminates_iff, ← head_terminates_iff]
      exact terminates_congr (h 0)
    · intro a b ma mb
      rcases a with - | a <;> rcases b with - | b
      · trivial
      · injection mem_unique (Computation.mem_map _ ma) ((h 0 _).2 (Computation.mem_map _ mb))
      · injection mem_unique (Computation.mem_map _ ma) ((h 0 _).2 (Computation.mem_map _ mb))
      · obtain ⟨a, s'⟩ := a
        obtain ⟨b, t'⟩ := b
        injection mem_unique (Computation.mem_map _ ma) ((h 0 _).2 (Computation.mem_map _ mb)) with
          ab
        refine ⟨ab, fun n => ?_⟩
        refine
          (get?_congr (flatten_equiv (Computation.mem_map _ ma)) n).symm.trans
            ((?_ : get? (tail s) n ~ get? (tail t) n).trans
              (get?_congr (flatten_equiv (Computation.mem_map _ mb)) n))
        rw [get?_tail]; rw [get?_tail]
        apply h⟩

/--
theorem `liftRel_map` / 定理 `liftRel_map`

English:
theorem liftRel_map
  statement: {δ} (R : α -> β -> Prop) (S : γ -> δ -> Prop) {s1 : WSeq α} {s2 : WSeq β}
  proof: ⟨fun s1 s2 => exists s t, s1 = map f1 s ∧ s2 = map f2 t ∧ LiftRel R s t, ⟨s1, s2, rfl, rfl, h1⟩,
    fun {s1 s2} h =>
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl, h⟩ => by
      simp only [exists_and_left, destruct_map]
      apply Computation.liftRel_map _ _ (liftRel_destruct h)
      intr

中文:
定理 liftRel_map
  结论: {δ} (R : α -> β -> 命题) (S : γ -> δ -> 命题) {s1 : WSeq α} {s2 : WSeq β}
  证明: ⟨fun s1 s2 => exists s t, s1 = map f1 s ∧ s2 = map f2 t ∧ LiftRel R s t, ⟨s1, s2, rfl, rfl, h1⟩,
    fun {s1 s2} h =>
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl, h⟩ => by
      simp only [exists_and_left, destruct_map]
      apply Computation.liftRel_map _ _ (liftRel_destruct h)
      intr

Depends on / 依赖: Computation, Computation.liftRel_map, LiftRel, destruct_map, exists_and_left, liftRel_destruct, liftRel_map
-/
theorem liftRel_map {δ} (R : α -> β -> Prop) (S : γ -> δ -> Prop) {s1 : WSeq α} {s2 : WSeq β}
    {f1 : α -> γ} {f2 : β -> δ} (h1 : LiftRel R s1 s2) (h2 : forall {a b}, R a b -> S (f1 a) (f2 b)) :
    LiftRel S (map f1 s1) (map f2 s2) :=
  ⟨fun s1 s2 => exists s t, s1 = map f1 s ∧ s2 = map f2 t ∧ LiftRel R s t, ⟨s1, s2, rfl, rfl, h1⟩,
    fun {s1 s2} h =>
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl, h⟩ => by
      simp only [exists_and_left, destruct_map]
      apply Computation.liftRel_map _ _ (liftRel_destruct h)
      intro o p h
      rcases o with - | a <;> rcases p with - | b
      · simp
      · cases b; cases h
      · cases a; cases h
      · obtain ⟨a, s⟩ := a; obtain ⟨b, t⟩ := b
        obtain ⟨r, h⟩ := h
        exact ⟨h2 r, s, rfl, t, rfl, h⟩⟩

/--
theorem `map_congr` / 定理 `map_congr`

English:
theorem map_congr
  given: (f : α -> β) {s t : WSeq α} (h : s ~ʷ t)
  statement: map f s ~ʷ map f t
  proof: liftRel_map _ _ h fun {_ _} => congr_arg _

中文:
定理 map_congr
  条件: (f : α -> β) {s t : WSeq α} (h : s ~ʷ t)
  结论: map f s ~ʷ map f t
  证明: liftRel_map _ _ h fun {_ _} => congr_arg _

Depends on / 依赖: congr_arg, liftRel_map
-/
theorem map_congr (f : α -> β) {s t : WSeq α} (h : s ~ʷ t) : map f s ~ʷ map f t :=
  liftRel_map _ _ h fun {_ _} => congr_arg _

/--
theorem `liftRel_append` / 定理 `liftRel_append`

English:
theorem liftRel_append
  statement: (R : α -> β -> Prop) {s1 s2 : WSeq α} {t1 t2 : WSeq β} (h1 : LiftRel R s1 t1)
  proof: ⟨fun s t => LiftRel R s t ∨ exists s1 t1, s = append s1 s2 ∧ t = append t1 t2 ∧ LiftRel R s1 t1,
    Or.inr ⟨s1, t1, rfl, rfl, h1⟩, fun {s t} h =>
    match s, t, h with
    | s, t, Or.inl h => by
      apply Computation.LiftRel.imp _ _ _ (liftRel_destruct h)
      intro a b; apply LiftRelO.imp_righ

中文:
定理 liftRel_append
  结论: (R : α -> β -> 命题) {s1 s2 : WSeq α} {t1 t2 : WSeq β} (h1 : LiftRel R s1 t1)
  证明: ⟨fun s t => LiftRel R s t ∨ exists s1 t1, s = append s1 s2 ∧ t = append t1 t2 ∧ LiftRel R s1 t1,
    Or.inr ⟨s1, t1, rfl, rfl, h1⟩, fun {s t} h =>
    match s, t, h with
    | s, t, Or.inl h => by
      apply Computation.LiftRel.imp _ _ _ (liftRel_destruct h)
      intro a b; apply LiftRelO.imp_righ

Depends on / 依赖: Computation, Computation.LiftRel.imp, Computation.liftRel_bind, LiftRel, LiftRelO, LiftRelO.imp_right, Or.inl, Or.inr, append, destruct_append, exists_and_left, imp_right, liftRel_bind, liftRel_destruct
-/
theorem liftRel_append (R : α -> β -> Prop) {s1 s2 : WSeq α} {t1 t2 : WSeq β} (h1 : LiftRel R s1 t1)
    (h2 : LiftRel R s2 t2) : LiftRel R (append s1 s2) (append t1 t2) :=
  ⟨fun s t => LiftRel R s t ∨ exists s1 t1, s = append s1 s2 ∧ t = append t1 t2 ∧ LiftRel R s1 t1,
    Or.inr ⟨s1, t1, rfl, rfl, h1⟩, fun {s t} h =>
    match s, t, h with
    | s, t, Or.inl h => by
      apply Computation.LiftRel.imp _ _ _ (liftRel_destruct h)
      intro a b; apply LiftRelO.imp_right
      intro s t; apply Or.inl
    | _, _, Or.inr ⟨s1, t1, rfl, rfl, h⟩ => by
      simp only [exists_and_left, destruct_append]
      apply Computation.liftRel_bind _ _ (liftRel_destruct h)
      intro o p h
      rcases o with - | a <;> rcases p with - | b
      · simp only [destruct_append.aux]
        apply Computation.LiftRel.imp _ _ _ (liftRel_destruct h2)
        intro a b
        apply LiftRelO.imp_right
        intro s t
        apply Or.inl
      · cases b; cases h
      · cases a; cases h
      · obtain ⟨a, s⟩ := a; obtain ⟨b, t⟩ := b
        obtain ⟨r, h⟩ := h
        simpa using ⟨r, Or.inr ⟨s, rfl, t, rfl, h⟩⟩⟩

/--
theorem `liftRel_join.lem` / 定理 `liftRel_join.lem`

English:
theorem liftRel_join.lem
  statement: (R : α -> β -> Prop) {S T} {U : WSeq α -> WSeq β -> Prop}
  proof: by
  obtain ⟨n, h⟩ := exists_results_of_mem ma; clear ma; revert S T ST a
  induction n using Nat.strongRecOn with | _ n IH
  intro S T ST a ra; simp only [destruct_join] at ra
  exact
    let ⟨o, m, k, rs1, rs2, en⟩ := of_results_bind ra
    let ⟨p, mT, rop⟩ := Computation.exists_of_liftRel_left (l

中文:
定理 liftRel_join.lem
  结论: (R : α -> β -> 命题) {S T} {U : WSeq α -> WSeq β -> 命题}
  证明: by
  obtain ⟨n, h⟩ := exists_results_of_mem ma; clear ma; revert S T ST a
  induction n using Nat.strongRecOn with | _ n IH
  intro S T ST a ra; simp only [destruct_join] at ra
  exact
    let ⟨o, m, k, rs1, rs2, en⟩ := of_results_bind ra
    let ⟨p, mT, rop⟩ := Computation.exists_of_liftRel_left (l

Depends on / 依赖: Computation, Computation.exists_of_liftRel_left, Nat.strongRecOn, destruct_join, eq_of_pure_mem, exists_of_liftRel_left, exists_results_of_mem, g.val, liftRel_destruct, mem_bind, of_results_bind, ret_mem, revert, rs1.mem, rs2.mem, strongRecOn
-/
theorem liftRel_join.lem (R : α -> β -> Prop) {S T} {U : WSeq α -> WSeq β -> Prop}
    (ST : LiftRel (LiftRel R) S T)
    (HU :
      forall s1 s2,
        (exists s t S T,
            s1 = append s (join S) ∧
              s2 = append t (join T) ∧ LiftRel R s t ∧ LiftRel (LiftRel R) S T) ->
          U s1 s2)
    {a} (ma : a in destruct (join S)) : exists b, b in destruct (join T) ∧ LiftRelO R U a b := by
  obtain ⟨n, h⟩ := exists_results_of_mem ma; clear ma; revert S T ST a
  induction n using Nat.strongRecOn with | _ n IH
  intro S T ST a ra; simp only [destruct_join] at ra
  exact
    let ⟨o, m, k, rs1, rs2, en⟩ := of_results_bind ra
    let ⟨p, mT, rop⟩ := Computation.exists_of_liftRel_left (liftRel_destruct ST) rs1.mem
    match o, p, rop, rs1, rs2, mT with
    | none, none, _, _, rs2, mT => by
      simp only [destruct_join]
      exact ⟨none, mem_bind mT (ret_mem _), by rw [eq_of_pure_mem rs2.mem]; trivial⟩
    | some (s, S'), some (t, T'), ⟨st, ST'⟩, _, rs2, mT => by
      simp? [destruct_append] at rs2 says simp only [destruct_join.aux, destruct_append] at rs2
      exact
        let ⟨k1, rs3, ek⟩ := of_results_think rs2
        let ⟨o', m1, n1, rs4, rs5, ek1⟩ := of_results_bind rs3
        let ⟨p', mt, rop'⟩ := Computation.exists_of_liftRel_left (liftRel_destruct st) rs4.mem
        match o', p', rop', rs4, rs5, mt with
        | none, none, _, _, rs5', mt => by
          have : n1 < n := by
            rw [en]; rw [ek]; rw [ek1]
            apply lt_of_lt_of_le _ (Nat.le_add_right _ _)
            apply Nat.lt_succ_of_le (Nat.le_add_right _ _)
          let ⟨ob, mb, rob⟩ := IH _ this ST' rs5'
          refine ⟨ob, ?_, rob⟩
          · simp +unfoldPartialApp only [destruct_join, destruct_join.aux]
            apply mem_bind mT
            simp only [destruct_append]
            apply think_mem
            apply mem_bind mt
            exact mb
        | some (a, s'), some (b, t'), ⟨ab, st'⟩, _, rs5, mt => by
          simp only [destruct_append.aux] at rs5
          refine ⟨some (b, append t' (join T')), ?_, ?_⟩
          · simp +unfoldPartialApp only [destruct_join, destruct_join.aux]
            apply mem_bind mT
            simp only [destruct_append]
            apply think_mem
            apply mem_bind mt
            apply ret_mem
          rw [eq_of_pure_mem rs5.mem]
          exact ⟨ab, HU _ _ ⟨s', t', S', T', rfl, rfl, st', ST'⟩⟩

/--
theorem `liftRel_join` / 定理 `liftRel_join`

English:
theorem liftRel_join
  statement: (R : α -> β -> Prop) {S : WSeq (WSeq α)} {T : WSeq (WSeq β)}
  proof: ⟨fun s1 s2 =>
    exists s t S T,
      s1 = append s (join S) ∧ s2 = append t (join T) ∧ LiftRel R s t ∧ LiftRel (LiftRel R) S T,
    ⟨nil, nil, S, T, by simp, by simp, by simp, h⟩, fun {s1 s2} ⟨s, t, S, T, h1, h2, st, ST⟩ => by
    rw [h1]; rw [h2]; rw [destruct_append, destruct_append]
    apply 

中文:
定理 liftRel_join
  结论: (R : α -> β -> 命题) {S : WSeq (WSeq α)} {T : WSeq (WSeq β)}
  证明: ⟨fun s1 s2 =>
    exists s t S T,
      s1 = append s (join S) ∧ s2 = append t (join T) ∧ LiftRel R s t ∧ LiftRel (LiftRel R) S T,
    ⟨nil, nil, S, T, by simp, by simp, by simp, h⟩, fun {s1 s2} ⟨s, t, S, T, h1, h2, st, ST⟩ => by
    rw [h1]; rw [h2]; rw [destruct_append, destruct_append]
    apply 

Depends on / 依赖: Computation, Computation.liftRel_bind, LiftRel, append, destruct_append, liftRel_bind, liftRel_destruct
-/
theorem liftRel_join (R : α -> β -> Prop) {S : WSeq (WSeq α)} {T : WSeq (WSeq β)}
    (h : LiftRel (LiftRel R) S T) : LiftRel R (join S) (join T) :=
  ⟨fun s1 s2 =>
    exists s t S T,
      s1 = append s (join S) ∧ s2 = append t (join T) ∧ LiftRel R s t ∧ LiftRel (LiftRel R) S T,
    ⟨nil, nil, S, T, by simp, by simp, by simp, h⟩, fun {s1 s2} ⟨s, t, S, T, h1, h2, st, ST⟩ => by
    rw [h1]; rw [h2]; rw [destruct_append, destruct_append]
    apply Computation.liftRel_bind _ _ (liftRel_destruct st)
    exact fun {o p} h =>
      match o, p, h with
      | some (a, s), some (b, t), ⟨h1, h2⟩ => by
        simpa using ⟨h1, s, t, S, rfl, T, rfl, h2, ST⟩
      | none, none, _ => by
        -- We do not `dsimp` with `LiftRelO` since `liftRel_join.lem` uses `LiftRelO`.
        dsimp only [destruct_append.aux, Computation.LiftRel]; constructor
        · intro
          apply liftRel_join.lem _ ST fun _ _ => id
        · intro b mb
          rw [← LiftRelO.swap]
          apply liftRel_join.lem (swap R)
          · rw [← LiftRel.swap R, ← LiftRel.swap]
            apply ST
          · rw [← LiftRel.swap R, ← LiftRel.swap (LiftRel R)]
            exact fun s1 s2 ⟨s, t, S, T, h1, h2, st, ST⟩ => ⟨t, s, T, S, h2, h1, st, ST⟩
          · exact mb⟩

/--
theorem `join_congr` / 定理 `join_congr`

English:
theorem join_congr
  given: {S T : WSeq (WSeq α)} (h : LiftRel Equiv S T)
  statement: join S ~ʷ join T
  proof: liftRel_join _ h

中文:
定理 join_congr
  条件: {S T : WSeq (WSeq α)} (h : LiftRel 等价 S T)
  结论: join S ~ʷ join T
  证明: liftRel_join _ h

Depends on / 依赖: liftRel_join
-/
theorem join_congr {S T : WSeq (WSeq α)} (h : LiftRel Equiv S T) : join S ~ʷ join T :=
  liftRel_join _ h

/--
theorem `liftRel_bind` / 定理 `liftRel_bind`

English:
theorem liftRel_bind
  statement: {δ} (R : α -> β -> Prop) (S : γ -> δ -> Prop) {s1 : WSeq α} {s2 : WSeq β}
  proof: liftRel_join _ (liftRel_map _ _ h1 @h2)

中文:
定理 liftRel_bind
  结论: {δ} (R : α -> β -> 命题) (S : γ -> δ -> 命题) {s1 : WSeq α} {s2 : WSeq β}
  证明: liftRel_join _ (liftRel_map _ _ h1 @h2)

Depends on / 依赖: liftRel_join, liftRel_map
-/
theorem liftRel_bind {δ} (R : α -> β -> Prop) (S : γ -> δ -> Prop) {s1 : WSeq α} {s2 : WSeq β}
    {f1 : α -> WSeq γ} {f2 : β -> WSeq δ} (h1 : LiftRel R s1 s2)
    (h2 : forall {a b}, R a b -> LiftRel S (f1 a) (f2 b)) : LiftRel S (bind s1 f1) (bind s2 f2) :=
  liftRel_join _ (liftRel_map _ _ h1 @h2)

/--
theorem `bind_congr` / 定理 `bind_congr`

English:
theorem bind_congr
  given: {s1 s2 : WSeq α} {f1 f2 : α -> WSeq β} (h1 : s1 ~ʷ s2) (h2 : forall a, f1 a ~ʷ f2 a)
  proof: liftRel_bind _ _ h1 fun {a b} h => by rw [h]; apply h2

@[simp]

中文:
定理 bind_congr
  条件: {s1 s2 : WSeq α} {f1 f2 : α -> WSeq β} (h1 : s1 ~ʷ s2) (h2 : 对任意 a, f1 a ~ʷ f2 a)
  证明: liftRel_bind _ _ h1 fun {a b} h => by rw [h]; apply h2

@[simp]

Depends on / 依赖: liftRel_bind
-/
theorem bind_congr {s1 s2 : WSeq α} {f1 f2 : α -> WSeq β} (h1 : s1 ~ʷ s2) (h2 : forall a, f1 a ~ʷ f2 a) :
    bind s1 f1 ~ʷ bind s2 f2 :=
  liftRel_bind _ _ h1 fun {a b} h => by rw [h]; apply h2

@[simp]
/--
theorem `join_ret` / 定理 `join_ret`

English:
theorem join_ret
  given: (s : WSeq α)
  statement: join (ret s) ~ʷ s
  proof: by simpa [ret] using think_equiv _

@[simp]

中文:
定理 join_ret
  条件: (s : WSeq α)
  结论: join (ret s) ~ʷ s
  证明: by simpa [ret] using think_equiv _

@[simp]

Depends on / 依赖: think_equiv
-/
theorem join_ret (s : WSeq α) : join (ret s) ~ʷ s := by simpa [ret] using think_equiv _

@[simp]
/--
theorem `join_map_ret` / 定理 `join_map_ret`

English:
theorem join_map_ret
  given: (s : WSeq α)
  statement: join (map ret s) ~ʷ s
  proof: by
  refine ⟨fun s1 s2 => join (map ret s2) = s1, rfl, ?_⟩
  intro s' s h; rw [← h]
  apply liftRel_rec fun c1 c2 => exists s, c1 = destruct (join (map ret s)) ∧ c2 = destruct s
  · exact fun {c1 c2} h =>
      match c1, c2, h with
      | _, _, ⟨s, rfl, rfl⟩ => by
        clear h
        have (s : 

中文:
定理 join_map_ret
  条件: (s : WSeq α)
  结论: join (map ret s) ~ʷ s
  证明: by
  refine ⟨fun s1 s2 => join (map ret s2) = s1, rfl, ?_⟩
  intro s' s h; rw [← h]
  apply liftRel_rec fun c1 c2 => exists s, c1 = destruct (join (map ret s)) ∧ c2 = destruct s
  · exact fun {c1 c2} h =>
      match c1, c2, h with
      | _, _, ⟨s, rfl, rfl⟩ => by
        clear h
        have (s : 

Depends on / 依赖: WSeq.recOn, destruct, join.destruct, liftRel_rec
-/
theorem join_map_ret (s : WSeq α) : join (map ret s) ~ʷ s := by
  refine ⟨fun s1 s2 => join (map ret s2) = s1, rfl, ?_⟩
  intro s' s h; rw [← h]
  apply liftRel_rec fun c1 c2 => exists s, c1 = destruct (join (map ret s)) ∧ c2 = destruct s
  · exact fun {c1 c2} h =>
      match c1, c2, h with
      | _, _, ⟨s, rfl, rfl⟩ => by
        clear h
        have (s : WSeq α) : exists s' : WSeq α,
            (map ret s).join.destruct = (map ret s').join.destruct ∧ destruct s = s'.destruct :=
          ⟨s, rfl, rfl⟩
        induction s using WSeq.recOn <;> simp [ret, this]
  · exact ⟨s, rfl, rfl⟩

@[simp]
/--
theorem `join_append` / 定理 `join_append`

English:
theorem join_append
  given: (S T : WSeq (WSeq α))
  statement: join (append S T) ~ʷ append (join S) (join T)
  proof: by
  refine
    ⟨fun s1 s2 =>
      exists s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T)),
      ⟨nil, S, T, by simp, by simp⟩, ?_⟩
  intro s1 s2 h
  apply
    liftRel_rec
      (fun c1 c2 =>
        exists (s : WSeq α) (S T : _),
          c1 = destruct (append 

中文:
定理 join_append
  条件: (S T : WSeq (WSeq α))
  结论: join (append S T) ~ʷ append (join S) (join T)
  证明: by
  refine
    ⟨fun s1 s2 =>
      exists s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T)),
      ⟨nil, S, T, by simp, by simp⟩, ?_⟩
  intro s1 s2 h
  apply
    liftRel_rec
      (fun c1 c2 =>
        exists (s : WSeq α) (S T : _),
          c1 = destruct (append 

Depends on / 依赖: WSeq.recOn, append, congr_arg, destruct, liftRel_rec
-/
theorem join_append (S T : WSeq (WSeq α)) : join (append S T) ~ʷ append (join S) (join T) := by
  refine
    ⟨fun s1 s2 =>
      exists s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T)),
      ⟨nil, S, T, by simp, by simp⟩, ?_⟩
  intro s1 s2 h
  apply
    liftRel_rec
      (fun c1 c2 =>
        exists (s : WSeq α) (S T : _),
          c1 = destruct (append s (join (append S T))) ∧
            c2 = destruct (append s (append (join S) (join T))))
      _ _ _
      (let ⟨s, S, T, h1, h2⟩ := h
      ⟨s, S, T, congr_arg destruct h1, congr_arg destruct h2⟩)
  rintro c1 c2 ⟨s, S, T, rfl, rfl⟩
  induction s using WSeq.recOn with
  | nil =>
    induction S using WSeq.recOn with
    | nil =>
      simp only [nil_append, join_nil]
      induction T using WSeq.recOn with
      | nil => simp
      | cons s T =>
        simp only [join_cons, destruct_think, Computation.destruct_think, liftRelAux_inr_inr]
        refine ⟨s, nil, T, ?_, ?_⟩ <;> simp
      | think T =>
        simp only [join_think, destruct_think, Computation.destruct_think, liftRelAux_inr_inr]
        refine ⟨nil, nil, T, ?_, ?_⟩ <;> simp
    | cons s S => simpa using ⟨s, S, T, rfl, rfl⟩
    | think S => refine ⟨nil, S, T, ?_, ?_⟩ <;> simp
  | cons a s => simpa using ⟨s, S, T, rfl, rfl⟩
  | think s => simpa using ⟨s, S, T, rfl, rfl⟩

@[simp]
/--
theorem `bind_ret` / 定理 `bind_ret`

English:
theorem bind_ret
  given: (f : α -> β) (s)
  statement: bind s (ret ∘ f) ~ʷ map f s
  proof: by
  dsimp [bind]
  rw [map_comp]
  apply join_map_ret

@[simp]

中文:
定理 bind_ret
  条件: (f : α -> β) (s)
  结论: bind s (ret ∘ f) ~ʷ map f s
  证明: by
  dsimp [bind]
  rw [map_comp]
  apply join_map_ret

@[simp]

Depends on / 依赖: join_map_ret, map_comp
-/
theorem bind_ret (f : α -> β) (s) : bind s (ret ∘ f) ~ʷ map f s := by
  dsimp [bind]
  rw [map_comp]
  apply join_map_ret

@[simp]
/--
theorem `ret_bind` / 定理 `ret_bind`

English:
theorem ret_bind
  given: (a : α) (f : α -> WSeq β)
  statement: bind (ret a) f ~ʷ f a
  proof: by simp [bind]

@[simp]

中文:
定理 ret_bind
  条件: (a : α) (f : α -> WSeq β)
  结论: bind (ret a) f ~ʷ f a
  证明: by simp [bind]

@[simp]
-/
theorem ret_bind (a : α) (f : α -> WSeq β) : bind (ret a) f ~ʷ f a := by simp [bind]

@[simp]
/--
theorem `join_join` / 定理 `join_join`

English:
theorem join_join
  given: (SS : WSeq (WSeq (WSeq α)))
  statement: join (join SS) ~ʷ join (map join SS)
  proof: by
  refine
    ⟨fun s1 s2 =>
      exists s S SS,
        s1 = append s (join (append S (join SS))) ∧
          s2 = append s (append (join S) (join (map join SS))),
      ⟨nil, nil, SS, by simp, by simp⟩, ?_⟩
  intro s1 s2 h
  apply
    liftRel_rec
      (fun c1 c2 =>
        exists s S SS,
      

中文:
定理 join_join
  条件: (SS : WSeq (WSeq (WSeq α)))
  结论: join (join SS) ~ʷ join (map join SS)
  证明: by
  refine
    ⟨fun s1 s2 =>
      exists s S SS,
        s1 = append s (join (append S (join SS))) ∧
          s2 = append s (append (join S) (join (map join SS))),
      ⟨nil, nil, SS, by simp, by simp⟩, ?_⟩
  intro s1 s2 h
  apply
    liftRel_rec
      (fun c1 c2 =>
        exists s S SS,
      

Depends on / 依赖: append, destruct, liftRel_rec
-/
theorem join_join (SS : WSeq (WSeq (WSeq α))) : join (join SS) ~ʷ join (map join SS) := by
  refine
    ⟨fun s1 s2 =>
      exists s S SS,
        s1 = append s (join (append S (join SS))) ∧
          s2 = append s (append (join S) (join (map join SS))),
      ⟨nil, nil, SS, by simp, by simp⟩, ?_⟩
  intro s1 s2 h
  apply
    liftRel_rec
      (fun c1 c2 =>
        exists s S SS,
          c1 = destruct (append s (join (append S (join SS)))) ∧
            c2 = destruct (append s (append (join S) (join (map join SS)))))
      _ (destruct s1) (destruct s2)
      (let ⟨s, S, SS, h1, h2⟩ := h
      ⟨s, S, SS, by simp [h1], by simp [h2]⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | _, _, ⟨s, S, SS, rfl, rfl⟩ => by
      clear h
      induction s using WSeq.recOn with
      | nil =>
        induction S using WSeq.recOn with
        | nil =>
          simp only [nil_append, join_nil]
          induction SS using WSeq.recOn with
          | nil => simp
          | cons S SS => refine ⟨nil, S, SS, ?_, ?_⟩ <;> simp
          | think SS => refine ⟨nil, nil, SS, ?_, ?_⟩ <;> simp
        | cons s S => simpa using ⟨s, S, SS, rfl, rfl⟩
        | think S => refine ⟨nil, S, SS, ?_, ?_⟩ <;> simp
      | cons a s => simpa using ⟨s, S, SS, rfl, rfl⟩
      | think s => simpa using ⟨s, S, SS, rfl, rfl⟩

@[simp]
/--
theorem `bind_assoc_comp` / 定理 `bind_assoc_comp`

English:
theorem bind_assoc_comp
  given: (s : WSeq α) (f : α -> WSeq β) (g : β -> WSeq γ)
  proof: by
  simp only [bind, map_join]
  rw [← map_comp f (map g)]; rw [← Function.comp_def]; rw [comp_assoc]; rw [map_comp (map g ∘ f) join s]
  exact join_join (map (map g ∘ f) s)

@[simp]

中文:
定理 bind_assoc_comp
  条件: (s : WSeq α) (f : α -> WSeq β) (g : β -> WSeq γ)
  证明: by
  simp only [bind, map_join]
  rw [← map_comp f (map g)]; rw [← Function.comp_def]; rw [comp_assoc]; rw [map_comp (map g ∘ f) join s]
  exact join_join (map (map g ∘ f) s)

@[simp]

Depends on / 依赖: Function, Function.comp_def, comp_assoc, comp_def, join_join, map_comp, map_join
-/
theorem bind_assoc_comp (s : WSeq α) (f : α -> WSeq β) (g : β -> WSeq γ) :
    bind (bind s f) g ~ʷ bind s ((fun y : WSeq β => bind y g) ∘ f) := by
  simp only [bind, map_join]
  rw [← map_comp f (map g)]; rw [← Function.comp_def]; rw [comp_assoc]; rw [map_comp (map g ∘ f) join s]
  exact join_join (map (map g ∘ f) s)

@[simp]
/--
theorem `bind_assoc` / 定理 `bind_assoc`

English:
theorem bind_assoc
  given: (s : WSeq α) (f : α -> WSeq β) (g : β -> WSeq γ)
  proof: by
  exact bind_assoc_comp s f g

中文:
定理 bind_assoc
  条件: (s : WSeq α) (f : α -> WSeq β) (g : β -> WSeq γ)
  证明: by
  exact bind_assoc_comp s f g

Depends on / 依赖: bind_assoc_comp
-/
theorem bind_assoc (s : WSeq α) (f : α -> WSeq β) (g : β -> WSeq γ) :
    bind (bind s f) g ~ʷ bind s fun x : α => bind (f x) g := by
  exact bind_assoc_comp s f g

end Stream'.WSeq
