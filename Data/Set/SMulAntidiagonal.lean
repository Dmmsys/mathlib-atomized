/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Order.AddTorsor
public import Mathlib.Order.WellFoundedSet

/-!
# Antidiagonal for scalar multiplication

Given partially ordered sets `G` and `P`, with an action of `G` on `P`, we construct, for any
element `a` in `P` and subsets `s` in `G` and `t` in `P`, the set of all pairs of an element in `s`
and an element in `t` that scalar-multiply to `a`.

## Definitions
* SMul.antidiagonal : Set-valued antidiagonal for SMul.
* VAdd.antidiagonal : Set-valued antidiagonal for VAdd.
-/

@[expose] public section

variable {G P : Type*}

namespace Set

section SMul

variable [SMul G P] {s s₁ s₂ : Set G} {t t₁ t₂ : Set P} {a : P} {x : G × P}

/-- `smulAntidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
that scalar multiply to `a`. -/
@[to_additive /-- `vaddAntidiagonal s t a` is the set of all pairs of an element in `s` and an
      element in `t` that vector-add to `a`. -/]
/--
Definition of `smulAntidiagonal` / `smulAntidiagonal` 的定义

English:
definition smulAntidiagonal
  signature: (s : Set G) (t : Set P) (a : P)
  body: { x | x.1 in s ∧ x.2 in t ∧ x.1 • x.2 = a }

@[to_additive (attr := simp)]

中文:
定义 smulAntidiagonal
  签名: (s : 集合 G) (t : 集合 P) (a : P)
  定义体: { x | x.1 in s ∧ x.2 in t ∧ x.1 • x.2 = a }

@[to_additive (attr := simp)]
-/
def smulAntidiagonal (s : Set G) (t : Set P) (a : P) : Set (G × P) :=
  { x | x.1 in s ∧ x.2 in t ∧ x.1 • x.2 = a }

@[to_additive (attr := simp)]
/--
theorem `mem_smulAntidiagonal` / 定理 `mem_smulAntidiagonal`

English:
theorem mem_smulAntidiagonal
  statement: x in smulAntidiagonal s t a ↔ x.1 in s ∧ x.2 in t ∧ x.1 • x.2 = a
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_smulAntidiagonal
  结论: x in smulAntidiagonal s t a ↔ x.1 in s ∧ x.2 in t ∧ x.1 • x.2 = a
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_smulAntidiagonal : x in smulAntidiagonal s t a ↔ x.1 in s ∧ x.2 in t ∧ x.1 • x.2 = a :=
  Iff.rfl

@[to_additive]
/--
theorem `smulAntidiagonal_mono_left` / 定理 `smulAntidiagonal_mono_left`

English:
theorem smulAntidiagonal_mono_left
  given: (h : s₁ subseteq s₂)
  proof: fun _ hx => ⟨h hx.1, hx.2.1, hx.2.2⟩

@[to_additive]

中文:
定理 smulAntidiagonal_mono_left
  条件: (h : s₁ subseteq s₂)
  证明: fun _ hx => ⟨h hx.1, hx.2.1, hx.2.2⟩

@[to_additive]
-/
theorem smulAntidiagonal_mono_left (h : s₁ subseteq s₂) :
    smulAntidiagonal s₁ t a subseteq smulAntidiagonal s₂ t a :=
  fun _ hx => ⟨h hx.1, hx.2.1, hx.2.2⟩

@[to_additive]
/--
theorem `smulAntidiagonal_mono_right` / 定理 `smulAntidiagonal_mono_right`

English:
theorem smulAntidiagonal_mono_right
  given: (h : t₁ subseteq t₂)
  proof: fun _ hx => ⟨hx.1, h hx.2.1, hx.2.2⟩

中文:
定理 smulAntidiagonal_mono_right
  条件: (h : t₁ subseteq t₂)
  证明: fun _ hx => ⟨hx.1, h hx.2.1, hx.2.2⟩
-/
theorem smulAntidiagonal_mono_right (h : t₁ subseteq t₂) :
    smulAntidiagonal s t₁ a subseteq smulAntidiagonal s t₂ a := fun _ hx => ⟨hx.1, h hx.2.1, hx.2.2⟩

end SMul

open SMul

namespace SMulAntidiagonal

variable {s : Set G} {t : Set P} {a : P}

section CancelSMul

variable [SMul G P] {x y : smulAntidiagonal s t a}

@[to_additive VAddAntidiagonal.fst_eq_fst_iff_snd_eq_snd]
/--
theorem `fst_eq_fst_iff_snd_eq_snd` / 定理 `fst_eq_fst_iff_snd_eq_snd`

English:
theorem fst_eq_fst_iff_snd_eq_snd
  given: [IsCancelSMul G P]
  proof: ⟨fun h =>
    IsCancelSMul.left_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    IsCancelSMul.right_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩

@[to_additive VAddAntidiagonal.eq_of_fst_

中文:
定理 fst_eq_fst_iff_snd_eq_snd
  条件: [是消去标量乘法 G P]
  证明: ⟨fun h =>
    IsCancelSMul.left_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    IsCancelSMul.right_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩

@[to_additive VAddAntidiagonal.eq_of_fst_

Depends on / 依赖: IsCancelSMul, IsCancelSMul.left_cancel, IsCancelSMul.right_cancel, left_cancel, right_cancel
-/
theorem fst_eq_fst_iff_snd_eq_snd [IsCancelSMul G P] :
    (x : G × P).1 = (y : G × P).1 ↔ (x : G × P).2 = (y : G × P).2 :=
  ⟨fun h =>
    IsCancelSMul.left_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    IsCancelSMul.right_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩

@[to_additive VAddAntidiagonal.eq_of_fst_eq_fst]
/--
theorem `eq_of_fst_eq_fst` / 定理 `eq_of_fst_eq_fst`

English:
theorem eq_of_fst_eq_fst
  given: [IsLeftCancelSMul G P] (h : (x : G × P).fst = (y : G × P).fst)
  statement: x = y
  proof: Subtype.ext Prod.ext h IsLeftCancelSMul.left_cancel _ _ _
    (y.2.2.2.trans <| by rw [← h]; exact x.2.2.2.symm).symm

@[to_additive VAddAntidiagonal.finite_of_finite]

中文:
定理 eq_of_fst_eq_fst
  条件: [是左消去标量乘法 G P] (h : (x : G × P).fst = (y : G × P).fst)
  结论: x = y
  证明: Subtype.ext Prod.ext h IsLeftCancelSMul.left_cancel _ _ _
    (y.2.2.2.trans <| by rw [← h]; exact x.2.2.2.symm).symm

@[to_additive VAddAntidiagonal.finite_of_finite]

Depends on / 依赖: IsLeftCancelSMul, IsLeftCancelSMul.left_cancel, Prod.ext, Subtype, Subtype.ext, left_cancel
-/
theorem eq_of_fst_eq_fst [IsLeftCancelSMul G P] (h : (x : G × P).fst = (y : G × P).fst) : x = y :=
Subtype.ext Prod.ext h IsLeftCancelSMul.left_cancel _ _ _
    (y.2.2.2.trans <| by rw [← h]; exact x.2.2.2.symm).symm

@[to_additive VAddAntidiagonal.finite_of_finite]
/--
theorem `finite_of_finite_fst` / 定理 `finite_of_finite_fst`

English:
theorem finite_of_finite_fst
  given: [IsLeftCancelSMul G P] (hs : s.Finite) (t) (p : P)
  proof: hs.of_injOn (fun _ ⟨h, _⟩ => h) fun _ _ _ _ _ => by
    grind only [mem_smulAntidiagonal, IsLeftCancelSMul.left_cancel]

@[to_additive VAddAntidiagonal.eq_of_snd_eq_snd]

中文:
定理 finite_of_finite_fst
  条件: [是左消去标量乘法 G P] (hs : s.有限) (t) (p : P)
  证明: hs.of_injOn (fun _ ⟨h, _⟩ => h) fun _ _ _ _ _ => by
    grind only [mem_smulAntidiagonal, IsLeftCancelSMul.left_cancel]

@[to_additive VAddAntidiagonal.eq_of_snd_eq_snd]

Depends on / 依赖: IsLeftCancelSMul, IsLeftCancelSMul.left_cancel, hs.of_injOn, left_cancel, mem_smulAntidiagonal, of_injOn
-/
theorem finite_of_finite_fst [IsLeftCancelSMul G P] (hs : s.Finite) (t) (p : P) :
    (s.smulAntidiagonal t p).Finite :=
  hs.of_injOn (fun _ ⟨h, _⟩ => h) fun _ _ _ _ _ => by
    grind only [mem_smulAntidiagonal, IsLeftCancelSMul.left_cancel]

@[to_additive VAddAntidiagonal.eq_of_snd_eq_snd]
/--
theorem `eq_of_snd_eq_snd` / 定理 `eq_of_snd_eq_snd`

English:
theorem eq_of_snd_eq_snd
  given: [IsCancelSMul G P] (h : (x : G × P).snd = (y : G × P).snd)
  statement: x = y
  proof: Subtype.ext Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

中文:
定理 eq_of_snd_eq_snd
  条件: [是消去标量乘法 G P] (h : (x : G × P).snd = (y : G × P).snd)
  结论: x = y
  证明: Subtype.ext Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

Depends on / 依赖: Prod.ext, Subtype, Subtype.ext, fst_eq_fst_iff_snd_eq_snd
-/
theorem eq_of_snd_eq_snd [IsCancelSMul G P] (h : (x : G × P).snd = (y : G × P).snd) : x = y :=
Subtype.ext Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

end CancelSMul

variable [PartialOrder G] [PartialOrder P] [SMul G P] [IsOrderedCancelSMul G P]
  {x y : smulAntidiagonal s t a}

@[to_additive VAddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd]
/--
theorem `eq_of_fst_le_fst_of_snd_le_snd` / 定理 `eq_of_fst_le_fst_of_snd_le_snd`

English:
theorem eq_of_fst_le_fst_of_snd_le_snd
  statement: (h₁ : (x : G × P).1 <= (y : G × P).1)
  proof: eq_of_fst_eq_fst
    h₁.eq_of_not_lt fun hlt =>
(smul_lt_smul_of_lt_of_le hlt h₂).ne
        (mem_smulAntidiagonal.1 x.2).2.2.trans (mem_smulAntidiagonal.1 y.2).2.2.symm

@[to_additive VAddAntidiagonal.finite_of_isPWO]

中文:
定理 eq_of_fst_le_fst_of_snd_le_snd
  结论: (h₁ : (x : G × P).1 <= (y : G × P).1)
  证明: eq_of_fst_eq_fst
    h₁.eq_of_not_lt fun hlt =>
(smul_lt_smul_of_lt_of_le hlt h₂).ne
        (mem_smulAntidiagonal.1 x.2).2.2.trans (mem_smulAntidiagonal.1 y.2).2.2.symm

@[to_additive VAddAntidiagonal.finite_of_isPWO]

Depends on / 依赖: eq_of_fst_eq_fst, eq_of_not_lt, mem_smulAntidiagonal, smul_lt_smul_of_lt_of_le
-/
theorem eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : G × P).1 <= (y : G × P).1)
    (h₂ : (x : G × P).2 <= (y : G × P).2) : x = y :=
eq_of_fst_eq_fst
    h₁.eq_of_not_lt fun hlt =>
(smul_lt_smul_of_lt_of_le hlt h₂).ne
        (mem_smulAntidiagonal.1 x.2).2.2.trans (mem_smulAntidiagonal.1 y.2).2.2.symm

@[to_additive VAddAntidiagonal.finite_of_isPWO]
/--
theorem `finite_of_isPWO` / 定理 `finite_of_isPWO`

English:
theorem finite_of_isPWO
  given: (hs : s.IsPWO) (ht : t.IsPWO) (a)
  statement: (smulAntidiagonal s t a).Finite
  proof: by
  by_contra! h
  have h1 : (smulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· <= ·)) :=
    fun f => hs fun n => ⟨_, (mem_smulAntidiagonal.1 (f n).2).1⟩
  have h2 : (smulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· <= ·)) :=
    fun f => ht fun n => ⟨_, (mem_smulAnt

中文:
定理 finite_of_isPWO
  条件: (hs : s.IsPWO) (ht : t.IsPWO) (a)
  结论: (smulAntidiagonal s t a).有限
  证明: by
  by_contra! h
  have h1 : (smulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· <= ·)) :=
    fun f => hs fun n => ⟨_, (mem_smulAntidiagonal.1 (f n).2).1⟩
  have h2 : (smulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· <= ·)) :=
    fun f => ht fun n => ⟨_, (mem_smulAnt

Depends on / 依赖: PartiallyWellOrderedOn, Prod.fst, Prod.snd, exists_monotone_subseq, g.injective, h.natEmbedding, h1.exists_monotone_subseq, injecti, injective, mem_smulAntidiagonal, mn.ne, natEmbedding, smulAntidiagonal
-/
theorem finite_of_isPWO (hs : s.IsPWO) (ht : t.IsPWO) (a) : (smulAntidiagonal s t a).Finite := by
  by_contra! h
  have h1 : (smulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· <= ·)) :=
    fun f => hs fun n => ⟨_, (mem_smulAntidiagonal.1 (f n).2).1⟩
  have h2 : (smulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· <= ·)) :=
    fun f => ht fun n => ⟨_, (mem_smulAntidiagonal.1 (f n).2).2.1⟩
  obtain ⟨g, hg⟩ := h1.exists_monotone_subseq fun n => (h.natEmbedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 fun n => h.natEmbedding _ _
  refine mn.ne (g.injective <| (h.natEmbedding _).injective ?_)
  exact eq_of_fst_le_fst_of_snd_le_snd (hg _ _ mn.le) h2'

end Set.SMulAntidiagonal
