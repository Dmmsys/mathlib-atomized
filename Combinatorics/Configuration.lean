/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Projectivization.Constructions

/-!
# Configurations of Points and lines

This file introduces abstract configurations of points and lines, and proves some basic properties.

## Main definitions
* `Configuration.Nondegenerate`: Excludes certain degenerate configurations,
  and imposes uniqueness of intersection points.
* `Configuration.HasPoints`: A nondegenerate configuration in which
  every pair of lines has an intersection point.
* `Configuration.HasLines`: A nondegenerate configuration in which
  every pair of points has a line through them.
* `Configuration.lineCount`: The number of lines through a given point.
* `Configuration.pointCount`: The number of lines through a given line.

## Main statements
* `Configuration.HasLines.card_le`: `HasLines` implies `|P| ≤ |L|`.
* `Configuration.HasPoints.card_le`: `HasPoints` implies `|L| ≤ |P|`.
* `Configuration.HasLines.hasPoints`: `HasLines` and `|P| = |L|` implies `HasPoints`.
* `Configuration.HasPoints.hasLines`: `HasPoints` and `|P| = |L|` implies `HasLines`.

Together, these four statements say that any two of the following properties imply the third:
(a) `HasLines`, (b) `HasPoints`, (c) `|P| = |L|`.

-/

@[expose] public section


open Finset

namespace Configuration

variable (P L : Type*) [Membership P L]

/--
Definition of `Dual` / `Dual` 的定义

English:
definition Dual
  body: P

中文:
定义 Dual
  定义体: P
-/
def Dual :=
  P

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Inhabited P] : Inhabited (Dual P)
  body: h

中文:
实例 [h
  签名: : Inhabited P] : Inhabited (Dual P)
  定义体: h
-/
instance [h : Inhabited P] : Inhabited (Dual P) :=
  h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: P] : Finite (Dual P)
  body: ‹Finite P›

中文:
实例 [Finite
  签名: P] : Finite (Dual P)
  定义体: ‹Finite P›

Depends on / 依赖: Finite
-/
instance [Finite P] : Finite (Dual P) :=
  ‹Finite P›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Fintype P] : Fintype (Dual P)
  body: h

中文:
实例 [h
  签名: : Fintype P] : Fintype (Dual P)
  定义体: h
-/
instance [h : Fintype P] : Fintype (Dual P) :=
  h

set_option synthInstance.checkSynthOrder false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership (Dual L) (Dual P)
  body: ⟨Function.swap (Membership.mem : L -> P -> Prop)⟩

中文:
实例 :
  签名: Membership (Dual L) (Dual P)
  定义体: ⟨Function.swap (Membership.mem : L -> P -> Prop)⟩

Depends on / 依赖: Function, Function.swap, Membership, Membership.mem
-/
instance : Membership (Dual L) (Dual P) :=
  ⟨Function.swap (Membership.mem : L -> P -> Prop)⟩

/--
Definition of `Nondegenerate` / `Nondegenerate` 的定义

English:
class Nondegenerate
  parameters: : Prop where
  axioms and operations (3):
    - exists_point : forall l : L, exists p, p ∉ l
    - exists_line : forall p, exists l : L, p ∉ l
    - eq_or_eq : forall {p₁ p₂ : P} {l₁ l₂ : L}, p₁ in l₁ -> p₂ in l₁ -> p₁ in l₂ -> p₂ in l₂ -> p₁ = p₂ ∨ l₁ = l₂

中文:
类 Nondegenerate
  参数: : 命题 where
  公理与运算 (3 个):
    - exists_point : 对任意 l : L, 存在 p, p ∉ l
    - exists_line : 对任意 p, 存在 l : L, p ∉ l
    - eq_or_eq : 对任意 {p₁ p₂ : P} {l₁ l₂ : L}, p₁ in l₁ -> p₂ in l₁ -> p₁ in l₂ -> p₂ in l₂ -> p₁ = p₂ ∨ l₁ = l₂
-/
class Nondegenerate : Prop where
  exists_point : forall l : L, exists p, p ∉ l
  exists_line : forall p, exists l : L, p ∉ l
  eq_or_eq : forall {p₁ p₂ : P} {l₁ l₂ : L}, p₁ in l₁ -> p₂ in l₁ -> p₁ in l₂ -> p₂ in l₂ -> p₁ = p₂ ∨ l₁ = l₂

/--
Definition of `HasPoints` / `HasPoints` 的定义

English:
class HasPoints
  parameters: extends Nondegenerate P L
  extends: Nondegenerate P L
  axioms and operations (2):
    - mkPoint : forall {l₁ l₂ : L}, l₁ != l₂ -> P
    - mkPoint_ax : forall {l₁ l₂ : L} (h : l₁ != l₂), mkPoint h in l₁ ∧ mkPoint h in l₂

中文:
类 HasPoints
  参数: extends Nondegenerate P L
  继承: Nondegenerate P L
  公理与运算 (2 个):
    - mkPoint : 对任意 {l₁ l₂ : L}, l₁ != l₂ -> P
    - mkPoint_ax : 对任意 {l₁ l₂ : L} (h : l₁ != l₂), mkPoint h in l₁ ∧ mkPoint h in l₂
-/
class HasPoints extends Nondegenerate P L where
  /-- Intersection of two lines -/
  mkPoint : forall {l₁ l₂ : L}, l₁ != l₂ -> P
  mkPoint_ax : forall {l₁ l₂ : L} (h : l₁ != l₂), mkPoint h in l₁ ∧ mkPoint h in l₂

/--
Definition of `HasLines` / `HasLines` 的定义

English:
class HasLines
  parameters: extends Nondegenerate P L
  extends: Nondegenerate P L
  axioms and operations (2):
    - mkLine : forall {p₁ p₂ : P}, p₁ != p₂ -> L
    - mkLine_ax : forall {p₁ p₂ : P} (h : p₁ != p₂), p₁ in mkLine h ∧ p₂ in mkLine h

中文:
类 HasLines
  参数: extends Nondegenerate P L
  继承: Nondegenerate P L
  公理与运算 (2 个):
    - mkLine : 对任意 {p₁ p₂ : P}, p₁ != p₂ -> L
    - mkLine_ax : 对任意 {p₁ p₂ : P} (h : p₁ != p₂), p₁ in mkLine h ∧ p₂ in mkLine h
-/
class HasLines extends Nondegenerate P L where
  /-- Line through two points -/
  mkLine : forall {p₁ p₂ : P}, p₁ != p₂ -> L
  mkLine_ax : forall {p₁ p₂ : P} (h : p₁ != p₂), p₁ in mkLine h ∧ p₂ in mkLine h

open Nondegenerate

open HasPoints (mkPoint mkPoint_ax)

open HasLines (mkLine mkLine_ax)

/--
Instance `Dual.Nondegenerate` / 实例 `Dual.Nondegenerate`

English:
instance Dual.Nondegenerate
  signature: [Nondegenerate P L]
  body: @exists_line P L _ _
  exists_line := @exists_point P L _ _
  eq_or_eq := @fun l₁ l₂ p₁ p₂ h₁ h₂ h₃ h₄ => (@eq_or_eq P L _ _ p₁ p₂ l₁ l₂ h₁ h₃ h₂ h₄).symm

中文:
实例 Dual.Nondegenerate
  签名: [Nondegenerate P L]
  定义体: @exists_line P L _ _
  exists_line := @exists_point P L _ _
  eq_or_eq := @fun l₁ l₂ p₁ p₂ h₁ h₂ h₃ h₄ => (@eq_or_eq P L _ _ p₁ p₂ l₁ l₂ h₁ h₃ h₂ h₄).symm

Depends on / 依赖: exists_line
-/
instance Dual.Nondegenerate [Nondegenerate P L] : Nondegenerate (Dual L) (Dual P) where
  exists_point := @exists_line P L _ _
  exists_line := @exists_point P L _ _
  eq_or_eq := @fun l₁ l₂ p₁ p₂ h₁ h₂ h₃ h₄ => (@eq_or_eq P L _ _ p₁ p₂ l₁ l₂ h₁ h₃ h₂ h₄).symm

/--
Instance `Dual.hasLines` / 实例 `Dual.hasLines`

English:
instance Dual.hasLines
  signature: [HasPoints P L]
  body: { Dual.Nondegenerate _ _ with
    mkLine := @mkPoint P L _ _
    mkLine_ax := @mkPoint_ax P L _ _ }

中文:
实例 Dual.hasLines
  签名: [HasPoints P L]
  定义体: { Dual.Nondegenerate _ _ with
    mkLine := @mkPoint P L _ _
    mkLine_ax := @mkPoint_ax P L _ _ }

Depends on / 依赖: Dual.Nondegenerate, Nondegenerate, mkLine, mkLine_ax, mkPoint, mkPoint_ax
-/
instance Dual.hasLines [HasPoints P L] : HasLines (Dual L) (Dual P) :=
  { Dual.Nondegenerate _ _ with
    mkLine := @mkPoint P L _ _
    mkLine_ax := @mkPoint_ax P L _ _ }

/--
Instance `Dual.hasPoints` / 实例 `Dual.hasPoints`

English:
instance Dual.hasPoints
  signature: [HasLines P L]
  body: { Dual.Nondegenerate _ _ with
    mkPoint := @mkLine P L _ _
    mkPoint_ax := @mkLine_ax P L _ _ }

中文:
实例 Dual.hasPoints
  签名: [HasLines P L]
  定义体: { Dual.Nondegenerate _ _ with
    mkPoint := @mkLine P L _ _
    mkPoint_ax := @mkLine_ax P L _ _ }

Depends on / 依赖: Dual.Nondegenerate, Nondegenerate, mkLine, mkLine_ax, mkPoint, mkPoint_ax
-/
instance Dual.hasPoints [HasLines P L] : HasPoints (Dual L) (Dual P) :=
  { Dual.Nondegenerate _ _ with
    mkPoint := @mkLine P L _ _
    mkPoint_ax := @mkLine_ax P L _ _ }

/--
theorem `HasPoints.existsUnique_point` / 定理 `HasPoints.existsUnique_point`

English:
theorem HasPoints.existsUnique_point
  given: [HasPoints P L] (l₁ l₂ : L) (hl : l₁ != l₂)
  proof: ⟨mkPoint hl, mkPoint_ax hl, fun _ hp =>
    (eq_or_eq hp.1 (mkPoint_ax hl).1 hp.2 (mkPoint_ax hl).2).resolve_right hl⟩

中文:
定理 HasPoints.existsUnique_point
  条件: [HasPoints P L] (l₁ l₂ : L) (hl : l₁ != l₂)
  证明: ⟨mkPoint hl, mkPoint_ax hl, fun _ hp =>
    (eq_or_eq hp.1 (mkPoint_ax hl).1 hp.2 (mkPoint_ax hl).2).resolve_right hl⟩

Depends on / 依赖: eq_or_eq, mkPoint, mkPoint_ax, resolve_right
-/
theorem HasPoints.existsUnique_point [HasPoints P L] (l₁ l₂ : L) (hl : l₁ != l₂) :
    exists! p, p in l₁ ∧ p in l₂ :=
  ⟨mkPoint hl, mkPoint_ax hl, fun _ hp =>
    (eq_or_eq hp.1 (mkPoint_ax hl).1 hp.2 (mkPoint_ax hl).2).resolve_right hl⟩

/--
theorem `HasLines.existsUnique_line` / 定理 `HasLines.existsUnique_line`

English:
theorem HasLines.existsUnique_line
  given: [HasLines P L] (p₁ p₂ : P) (hp : p₁ != p₂)
  proof: HasPoints.existsUnique_point (Dual L) (Dual P) p₁ p₂ hp

中文:
定理 HasLines.existsUnique_line
  条件: [HasLines P L] (p₁ p₂ : P) (hp : p₁ != p₂)
  证明: HasPoints.existsUnique_point (Dual L) (Dual P) p₁ p₂ hp

Depends on / 依赖: HasPoints, HasPoints.existsUnique_point, existsUnique_point
-/
theorem HasLines.existsUnique_line [HasLines P L] (p₁ p₂ : P) (hp : p₁ != p₂) :
    exists! l : L, p₁ in l ∧ p₂ in l :=
  HasPoints.existsUnique_point (Dual L) (Dual P) p₁ p₂ hp

variable {P L}

/--
theorem `Nondegenerate.exists_injective_of_card_le` / 定理 `Nondegenerate.exists_injective_of_card_le`

English:
theorem Nondegenerate.exists_injective_of_card_le
  statement: [Nondegenerate P L] [Fintype P] [Fintype L]
  proof: by
  classical
    let t : L -> Finset P := fun l => Set.toFinset { p | p ∉ l }
    suffices forall s : Finset L, #s <= (s.biUnion t).card by
      -- Hall's marriage theorem
      obtain ⟨f, hf1, hf2⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp this
      exact ⟨f, hf1, fun l => 

中文:
定理 Nondegenerate.exists_injective_of_card_le
  结论: [Nondegenerate P L] [Fintype P] [Fintype L]
  证明: by
  classical
    let t : L -> Finset P := fun l => Set.toFinset { p | p ∉ l }
    suffices forall s : Finset L, #s <= (s.biUnion t).card by
      -- Hall's marriage theorem
      obtain ⟨f, hf1, hf2⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp this
      exact ⟨f, hf1, fun l => 

Depends on / 依赖: Finset, Set.toFinset, biUnion, classical, s.biUnion, toFinset
-/
theorem Nondegenerate.exists_injective_of_card_le [Nondegenerate P L] [Fintype P] [Fintype L]
    (h : Fintype.card L <= Fintype.card P) : exists f : L -> P, Function.Injective f ∧ forall l, f l ∉ l := by
  classical
    let t : L -> Finset P := fun l => Set.toFinset { p | p ∉ l }
    suffices forall s : Finset L, #s <= (s.biUnion t).card by
      -- Hall's marriage theorem
      obtain ⟨f, hf1, hf2⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp this
      exact ⟨f, hf1, fun l => Set.mem_toFinset.mp (hf2 l)⟩
    intro s
    by_cases hs₀ : #s = 0
    -- If `s = ∅`, then `#s = 0 ≤ #(s.bUnion t)`
    · simp_rw [hs₀, zero_le]
    by_cases hs₁ : #s = 1
    -- If `s = {l}`, then pick a point `p ∉ l`
    · obtain ⟨l, rfl⟩ := Finset.card_eq_one.mp hs₁
      obtain ⟨p, hl⟩ := exists_point (P := P) l
      rw [Finset.card_singleton]; rw [Finset.singleton_biUnion]; rw [Nat.one_le_iff_ne_zero]
      exact Finset.card_ne_zero_of_mem (Set.mem_toFinset.mpr hl)
    suffices #(s.biUnion t)ᶜ <= #sᶜ by
      -- Rephrase in terms of complements (uses `h`)
      rw [Finset.card_compl]; rw [Finset.card_compl]; rw [tsub_le_iff_left] at this
      replace := h.trans this
      rwa [← add_tsub_assoc_of_le s.card_le_univ, le_tsub_iff_left (le_add_left s.card_le_univ),
        add_le_add_iff_right] at this
    have hs₂ : #(s.biUnion t)ᶜ <= 1 := by
      -- At most one line through two points of `s`
      refine Finset.card_le_one_iff.mpr @fun p₁ p₂ hp₁ hp₂ => ?_
      simp_rw [t, Finset.mem_compl, Finset.mem_biUnion, not_exists, not_and,
        Set.mem_toFinset, Set.mem_ofPred_eq, Classical.not_not] at hp₁ hp₂
      obtain ⟨l₁, l₂, hl₁, hl₂, hl₃⟩ :=
        Finset.one_lt_card_iff.mp (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hs₀, hs₁⟩)
      exact (eq_or_eq (hp₁ l₁ hl₁) (hp₂ l₁ hl₁) (hp₁ l₂ hl₂) (hp₂ l₂ hl₂)).resolve_right hl₃
    by_cases hs₃ : #sᶜ = 0
    · rw [hs₃, Nat.le_zero]
      rw [Finset.card_compl]; rw [tsub_eq_zero_iff_le]; rw [(Finset.card_le_univ _).ge_iff_eq']; rw [eq_comm]; rw [Finset.card_eq_iff_eq_univ] at hs₃ ⊢
      rw [hs₃]
      rw [Finset.eq_univ_iff_forall] at hs₃ ⊢
      exact fun p =>
        Exists.elim (exists_line p) -- If `s = univ`, then show `s.bUnion t = univ`
        fun l hl => Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, Set.mem_toFinset.mpr hl⟩
    · exact hs₂.trans (Nat.one_le_iff_ne_zero.mpr hs₃)

-- If `s < univ`, then consequence of `hs₂`
variable (L)

/--
Definition of `lineCount` / `lineCount` 的定义

English:
definition lineCount
  signature: (p : P)
  body: Nat.card { l : L // p in l }

中文:
定义 lineCount
  签名: (p : P)
  定义体: Nat.card { l : L // p in l }

Depends on / 依赖: Nat.card
-/
noncomputable def lineCount (p : P) : Nat :=
  Nat.card { l : L // p in l }

variable (P) {L}

/--
Definition of `pointCount` / `pointCount` 的定义

English:
definition pointCount
  signature: (l : L)
  body: Nat.card { p : P // p in l }

中文:
定义 pointCount
  签名: (l : L)
  定义体: Nat.card { p : P // p in l }

Depends on / 依赖: Nat.card
-/
noncomputable def pointCount (l : L) : Nat :=
  Nat.card { p : P // p in l }

variable (L)

/--
theorem `sum_lineCount_eq_sum_pointCount` / 定理 `sum_lineCount_eq_sum_pointCount`

English:
theorem sum_lineCount_eq_sum_pointCount
  given: [Fintype P] [Fintype L]
  proof: by
  classical
    simp only [lineCount, pointCount, Nat.card_eq_fintype_card, ← Fintype.card_sigma]
    apply Fintype.card_congr
    calc
      (Σ p, { l : L // p in l }) ≃ { x : P × L // x.1 in x.2 } :=
        (Equiv.subtypeProdEquivSigmaSubtype (· in ·)).symm
      _ ≃ { x : L × P // x.2 in x.1 

中文:
定理 sum_lineCount_eq_sum_pointCount
  条件: [Fintype P] [Fintype L]
  证明: by
  classical
    simp only [lineCount, pointCount, Nat.card_eq_fintype_card, ← Fintype.card_sigma]
    apply Fintype.card_congr
    calc
      (Σ p, { l : L // p in l }) ≃ { x : P × L // x.1 in x.2 } :=
        (Equiv.subtypeProdEquivSigmaSubtype (· in ·)).symm
      _ ≃ { x : L × P // x.2 in x.1 

Depends on / 依赖: Equiv.prodComm, Equiv.subtypeProdEquivSigmaSubtype, Fintype, Fintype.card_congr, Fintype.card_sigma, Iff.rfl, Nat.card_eq_fintype_card, card_congr, card_eq_fintype_card, card_sigma, classical, lineCount, pointCount, prodComm, subtypeEquiv, subtypeProdEquivSigmaSubtype
-/
theorem sum_lineCount_eq_sum_pointCount [Fintype P] [Fintype L] :
    ∑ p : P, lineCount L p = ∑ l : L, pointCount P l := by
  classical
    simp only [lineCount, pointCount, Nat.card_eq_fintype_card, ← Fintype.card_sigma]
    apply Fintype.card_congr
    calc
      (Σ p, { l : L // p in l }) ≃ { x : P × L // x.1 in x.2 } :=
        (Equiv.subtypeProdEquivSigmaSubtype (· in ·)).symm
      _ ≃ { x : L × P // x.2 in x.1 } := (Equiv.prodComm P L).subtypeEquiv fun x => Iff.rfl
      _ ≃ Σ l, { p // p in l } := Equiv.subtypeProdEquivSigmaSubtype fun (l : L) (p : P) => p in l

variable {P L}

/--
theorem `HasLines.pointCount_le_lineCount` / 定理 `HasLines.pointCount_le_lineCount`

English:
theorem HasLines.pointCount_le_lineCount
  statement: [HasLines P L] {p : P} {l : L} (h : p ∉ l)
  proof: by
  by_cases hf : Infinite { p : P // p in l }
  · simp [pointCount]
  have := fintypeOfNotInfinite hf
  cases nonempty_fintype { l : L // p in l }
  rw [lineCount]; rw [pointCount]; rw [Nat.card_eq_fintype_card]; rw [Nat.card_eq_fintype_card]
  have : forall p' : { p // p in l }, p != p' := fun p'

中文:
定理 HasLines.pointCount_le_lineCount
  结论: [HasLines P L] {p : P} {l : L} (h : p ∉ l)
  证明: by
  by_cases hf : Infinite { p : P // p in l }
  · simp [pointCount]
  have := fintypeOfNotInfinite hf
  cases nonempty_fintype { l : L // p in l }
  rw [lineCount]; rw [pointCount]; rw [Nat.card_eq_fintype_card]; rw [Nat.card_eq_fintype_card]
  have : forall p' : { p // p in l }, p != p' := fun p'

Depends on / 依赖: Fintype, Fintype.card_le_of_injective, Infinite, Nat.card_eq_fintype_card, Subtype, Subtype.ext, card_eq_fintype_card, card_le_of_injective, congr_arg, eq_or_eq, fintypeOfNotInfinite, lineCount, mkLine, mkLine_ax, nonempty_fintype, pointCount
-/
theorem HasLines.pointCount_le_lineCount [HasLines P L] {p : P} {l : L} (h : p ∉ l)
    [Finite { l : L // p in l }] : pointCount P l <= lineCount L p := by
  by_cases hf : Infinite { p : P // p in l }
  · simp [pointCount]
  have := fintypeOfNotInfinite hf
  cases nonempty_fintype { l : L // p in l }
  rw [lineCount]; rw [pointCount]; rw [Nat.card_eq_fintype_card]; rw [Nat.card_eq_fintype_card]
  have : forall p' : { p // p in l }, p != p' := fun p' hp' => h ((congr_arg (· in l) hp').mpr p'.2)
  exact
    Fintype.card_le_of_injective (fun p' => ⟨mkLine (this p'), (mkLine_ax (this p')).1⟩)
      fun p₁ p₂ hp =>
      Subtype.ext ((eq_or_eq p₁.2 p₂.2 (mkLine_ax (this p₁)).2
            ((congr_arg (_ in ·) (Subtype.ext_iff.mp hp)).mpr (mkLine_ax (this p₂)).2)).resolve_right
          fun h' => (congr_arg (p ∉ ·) h').mp h (mkLine_ax (this p₁)).1)

/--
theorem `HasPoints.lineCount_le_pointCount` / 定理 `HasPoints.lineCount_le_pointCount`

English:
theorem HasPoints.lineCount_le_pointCount
  statement: [HasPoints P L] {p : P} {l : L} (h : p ∉ l)
  proof: @HasLines.pointCount_le_lineCount (Dual L) (Dual P) _ _ l p h hf

中文:
定理 HasPoints.lineCount_le_pointCount
  结论: [HasPoints P L] {p : P} {l : L} (h : p ∉ l)
  证明: @HasLines.pointCount_le_lineCount (Dual L) (Dual P) _ _ l p h hf

Depends on / 依赖: HasLines, HasLines.pointCount_le_lineCount, pointCount_le_lineCount
-/
theorem HasPoints.lineCount_le_pointCount [HasPoints P L] {p : P} {l : L} (h : p ∉ l)
    [hf : Finite { p : P // p in l }] : lineCount L p <= pointCount P l :=
  @HasLines.pointCount_le_lineCount (Dual L) (Dual P) _ _ l p h hf

variable (P L)

/--
theorem `HasLines.card_le` / 定理 `HasLines.card_le`

English:
theorem HasLines.card_le
  given: [HasLines P L] [Fintype P] [Fintype L]
  proof: by
  classical
  by_contra hc₂
  obtain ⟨f, hf₁, hf₂⟩ := Nondegenerate.exists_injective_of_card_le (le_of_not_ge hc₂)
  have :=
    calc
      ∑ p, lineCount L p = ∑ l, pointCount P l := sum_lineCount_eq_sum_pointCount P L
      _ <= ∑ l, lineCount L (f l) :=
        (Finset.sum_le_sum fun l _ => Ha

中文:
定理 HasLines.card_le
  条件: [HasLines P L] [Fintype P] [Fintype L]
  证明: by
  classical
  by_contra hc₂
  obtain ⟨f, hf₁, hf₂⟩ := Nondegenerate.exists_injective_of_card_le (le_of_not_ge hc₂)
  have :=
    calc
      ∑ p, lineCount L p = ∑ l, pointCount P l := sum_lineCount_eq_sum_pointCount P L
      _ <= ∑ l, lineCount L (f l) :=
        (Finset.sum_le_sum fun l _ => Ha

Depends on / 依赖: Finset, Finset.sum_le_sum, Fintype, Fintype.card_le_of_surjective, HasLines, HasLines.pointCount_le_lineCount, Nondegenerate, Nondegenerate.exists_injective_of_card_le, card_le_of_surjective, classical, exists_injective_of_card_le, le_of_not_ge, lineCount, not_forall, not_forall.mp, pointCount, pointCount_le_lineCount, sum_le_sum, sum_lineCount_eq_sum_pointCount, sum_lt_sum_
-/
theorem HasLines.card_le [HasLines P L] [Fintype P] [Fintype L] :
    Fintype.card P <= Fintype.card L := by
  classical
  by_contra hc₂
  obtain ⟨f, hf₁, hf₂⟩ := Nondegenerate.exists_injective_of_card_le (le_of_not_ge hc₂)
  have :=
    calc
      ∑ p, lineCount L p = ∑ l, pointCount P l := sum_lineCount_eq_sum_pointCount P L
      _ <= ∑ l, lineCount L (f l) :=
        (Finset.sum_le_sum fun l _ => HasLines.pointCount_le_lineCount (hf₂ l))
      _ = ∑ p in univ.map ⟨f, hf₁⟩, lineCount L p := by rw [sum_map]; dsimp
      _ < ∑ p, lineCount L p := by
        obtain ⟨p, hp⟩ := not_forall.mp (mt (Fintype.card_le_of_surjective f) hc₂)
        refine sum_lt_sum_of_subset (subset_univ _) (mem_univ p) ?_ ?_ fun p _ _ => zero_le
        · simpa only [Finset.mem_map, exists_prop, Finset.mem_univ, true_and]
        · rw [lineCount, Nat.card_eq_fintype_card, Fintype.card_pos_iff]
          obtain ⟨l, _⟩ := @exists_line P L _ _ p
          exact
            let := not_exists.mp hp l
            ⟨⟨mkLine this, (mkLine_ax this).2⟩⟩
  exact lt_irrefl _ this

/--
theorem `HasPoints.card_le` / 定理 `HasPoints.card_le`

English:
theorem HasPoints.card_le
  given: [HasPoints P L] [Fintype P] [Fintype L]
  proof: @HasLines.card_le (Dual L) (Dual P) _ _ _ _

中文:
定理 HasPoints.card_le
  条件: [HasPoints P L] [Fintype P] [Fintype L]
  证明: @HasLines.card_le (Dual L) (Dual P) _ _ _ _

Depends on / 依赖: HasLines, HasLines.card_le, card_le
-/
theorem HasPoints.card_le [HasPoints P L] [Fintype P] [Fintype L] :
    Fintype.card L <= Fintype.card P :=
  @HasLines.card_le (Dual L) (Dual P) _ _ _ _

variable {P L}

/--
theorem `HasLines.exists_bijective_of_card_eq` / 定理 `HasLines.exists_bijective_of_card_eq`

English:
theorem HasLines.exists_bijective_of_card_eq
  statement: [HasLines P L] [Fintype P] [Fintype L]
  proof: by
  obtain ⟨f, hf1, hf2⟩ := Nondegenerate.exists_injective_of_card_le (ge_of_eq h)
  have hf3 := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf1, h.symm⟩
  exact ⟨f, hf3, fun l => (sum_eq_sum_iff_of_le fun l _ => pointCount_le_lineCount (hf2 l)).1
((hf3.sum_comp _).trans (sum_lineCount_eq_sum

中文:
定理 HasLines.exists_bijective_of_card_eq
  结论: [HasLines P L] [Fintype P] [Fintype L]
  证明: by
  obtain ⟨f, hf1, hf2⟩ := Nondegenerate.exists_injective_of_card_le (ge_of_eq h)
  have hf3 := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf1, h.symm⟩
  exact ⟨f, hf3, fun l => (sum_eq_sum_iff_of_le fun l _ => pointCount_le_lineCount (hf2 l)).1
((hf3.sum_comp _).trans (sum_lineCount_eq_sum

Depends on / 依赖: Fintype, Fintype.bijective_iff_injective_and_card, Nondegenerate, Nondegenerate.exists_injective_of_card_le, bijective_iff_injective_and_card, exists_injective_of_card_le, ge_of_eq, h.symm, hf3.sum_comp, mem_univ, pointCount_le_lineCount, sum_comp, sum_eq_sum_iff_of_le, sum_lineCount_eq_sum_pointCount
-/
theorem HasLines.exists_bijective_of_card_eq [HasLines P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) :
    exists f : L -> P, Function.Bijective f ∧ forall l, pointCount P l = lineCount L (f l) := by
  obtain ⟨f, hf1, hf2⟩ := Nondegenerate.exists_injective_of_card_le (ge_of_eq h)
  have hf3 := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf1, h.symm⟩
  exact ⟨f, hf3, fun l => (sum_eq_sum_iff_of_le fun l _ => pointCount_le_lineCount (hf2 l)).1
((hf3.sum_comp _).trans (sum_lineCount_eq_sum_pointCount P L)).symm _ mem_univ _⟩

/--
theorem `HasLines.lineCount_eq_pointCount` / 定理 `HasLines.lineCount_eq_pointCount`

English:
theorem HasLines.lineCount_eq_pointCount
  statement: [HasLines P L] [Fintype P] [Fintype L]
  proof: by
  classical
    obtain ⟨f, hf1, hf2⟩ := HasLines.exists_bijective_of_card_eq hPL
    let s : Finset (P × L) := Set.toFinset { i | i.1 in i.2 }
    have step1 : ∑ i : P × L, lineCount L i.1 = ∑ i : P × L, pointCount P i.2 := by
      rw [← Finset.univ_product_univ]; rw [Finset.sum_product_right]; 

中文:
定理 HasLines.lineCount_eq_pointCount
  结论: [HasLines P L] [Fintype P] [Fintype L]
  证明: by
  classical
    obtain ⟨f, hf1, hf2⟩ := HasLines.exists_bijective_of_card_eq hPL
    let s : Finset (P × L) := Set.toFinset { i | i.1 in i.2 }
    have step1 : ∑ i : P × L, lineCount L i.1 = ∑ i : P × L, pointCount P i.2 := by
      rw [← Finset.univ_product_univ]; rw [Finset.sum_product_right]; 

Depends on / 依赖: Finset, Finset.card_univ, Finset.sum_const, Finset.sum_product, Finset.sum_product_right, Finset.univ, Finset.univ_product_univ, HasLines, HasLines.exists_bijective_of_card_eq, Set.toFinset, card_univ, classical, exists_bijective_of_card_eq, lineCount, pointCount, s.sum_finset_product, simp_rw, sum_const, sum_finset_product, sum_lineCount_eq_sum_pointCount
-/
theorem HasLines.lineCount_eq_pointCount [HasLines P L] [Fintype P] [Fintype L]
    (hPL : Fintype.card P = Fintype.card L) {p : P} {l : L} (hpl : p ∉ l) :
    lineCount L p = pointCount P l := by
  classical
    obtain ⟨f, hf1, hf2⟩ := HasLines.exists_bijective_of_card_eq hPL
    let s : Finset (P × L) := Set.toFinset { i | i.1 in i.2 }
    have step1 : ∑ i : P × L, lineCount L i.1 = ∑ i : P × L, pointCount P i.2 := by
      rw [← Finset.univ_product_univ]; rw [Finset.sum_product_right]; rw [Finset.sum_product]
      simp_rw [Finset.sum_const, Finset.card_univ, hPL, sum_lineCount_eq_sum_pointCount]
    have step2 : ∑ i in s, lineCount L i.1 = ∑ i in s, pointCount P i.2 := by
      rw [s.sum_finset_product Finset.univ fun p => Set.toFinset { l | p in l }]
      on_goal 1 =>
        rw [s.sum_finset_product_right Finset.univ fun l => Set.toFinset { p | p in l }]; rw [eq_comm]
        · refine sum_bijective _ hf1 (by simp) fun l _ => ?_
          simp_rw [hf2, sum_const, Set.toFinset_card, ← Nat.card_eq_fintype_card]
          change pointCount P l • _ = lineCount L (f l) • _
          rw [hf2]
      all_goals simp_rw [s, Finset.mem_univ, true_and, Set.mem_toFinset]; exact fun p => Iff.rfl
    have step3 : ∑ i in sᶜ, lineCount L i.1 = ∑ i in sᶜ, pointCount P i.2 := by
      rwa [← s.sum_add_sum_compl, ← s.sum_add_sum_compl, step2, add_left_cancel_iff] at step1
    rw [← Set.toFinset_compl] at step3
    exact
      ((Finset.sum_eq_sum_iff_of_le fun i hi =>
              HasLines.pointCount_le_lineCount (by exact Set.mem_toFinset.mp hi)).mp
          step3.symm (p, l) (Set.mem_toFinset.mpr hpl)).symm

/--
theorem `HasPoints.lineCount_eq_pointCount` / 定理 `HasPoints.lineCount_eq_pointCount`

English:
theorem HasPoints.lineCount_eq_pointCount
  statement: [HasPoints P L] [Fintype P] [Fintype L]
  proof: (@HasLines.lineCount_eq_pointCount (Dual L) (Dual P) _ _ _ _ hPL.symm l p hpl).symm

中文:
定理 HasPoints.lineCount_eq_pointCount
  结论: [HasPoints P L] [Fintype P] [Fintype L]
  证明: (@HasLines.lineCount_eq_pointCount (Dual L) (Dual P) _ _ _ _ hPL.symm l p hpl).symm

Depends on / 依赖: HasLines, HasLines.lineCount_eq_pointCount, hPL.symm, lineCount_eq_pointCount
-/
theorem HasPoints.lineCount_eq_pointCount [HasPoints P L] [Fintype P] [Fintype L]
    (hPL : Fintype.card P = Fintype.card L) {p : P} {l : L} (hpl : p ∉ l) :
    lineCount L p = pointCount P l :=
  (@HasLines.lineCount_eq_pointCount (Dual L) (Dual P) _ _ _ _ hPL.symm l p hpl).symm

/-- If a nondegenerate configuration has a unique line through any two points, and if `|P| = |L|`,
  then there is a unique point on any two lines. -/
@[instance_reducible]
/--
Definition of `HasLines.hasPoints` / `HasLines.hasPoints` 的定义

English:
definition HasLines.hasPoints
  signature: [HasLines P L] [Fintype P] [Fintype L]
  body: let : forall l₁ l₂ : L, l₁ != l₂ -> exists p : P, p in l₁ ∧ p in l₂ := fun l₁ l₂ hl => by
    classical
      obtain ⟨f, _, hf2⟩ := HasLines.exists_bijective_of_card_eq h
      have : Nontrivial L := ⟨⟨l₁, l₂, hl⟩⟩
      have := Fintype.one_lt_card_iff_nontrivial.mp ((congr_arg _ h).mpr Fintype.one_

中文:
定义 HasLines.hasPoints
  签名: [HasLines P L] [Fintype P] [Fintype L]
  定义体: let : forall l₁ l₂ : L, l₁ != l₂ -> exists p : P, p in l₁ ∧ p in l₂ := fun l₁ l₂ hl => by
    classical
      obtain ⟨f, _, hf2⟩ := HasLines.exists_bijective_of_card_eq h
      have : Nontrivial L := ⟨⟨l₁, l₂, hl⟩⟩
      have := Fintype.one_lt_card_iff_nontrivial.mp ((congr_arg _ h).mpr Fintype.one_

Depends on / 依赖: Exists, Exists.elim, Fintype, Fintype.card_pos_iff.mpr, Fintype.one_lt_card, Fintype.one_lt_card_iff_nontrivial.mp, HasLines, HasLines.exists_bijective_of_card_eq, Nat.card_eq_fintype_card, Nontrivial, card_eq_fintype_card, card_pos_iff, classical, congr_arg, exists_bijective_of_card_eq, exists_ne, lineCount, mkLine, mkLine_ax, one_lt_card
-/
noncomputable def HasLines.hasPoints [HasLines P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) : HasPoints P L :=
  let : forall l₁ l₂ : L, l₁ != l₂ -> exists p : P, p in l₁ ∧ p in l₂ := fun l₁ l₂ hl => by
    classical
      obtain ⟨f, _, hf2⟩ := HasLines.exists_bijective_of_card_eq h
      have : Nontrivial L := ⟨⟨l₁, l₂, hl⟩⟩
      have := Fintype.one_lt_card_iff_nontrivial.mp ((congr_arg _ h).mpr Fintype.one_lt_card)
      have h₁ : forall p : P, 0 < lineCount L p := fun p =>
        Exists.elim (exists_ne p) fun q hq =>
          (congr_arg _ Nat.card_eq_fintype_card).mpr
            (Fintype.card_pos_iff.mpr ⟨⟨mkLine hq, (mkLine_ax hq).2⟩⟩)
      have h₂ : forall l : L, 0 < pointCount P l := fun l => (congr_arg _ (hf2 l)).mpr (h₁ (f l))
      obtain ⟨p, hl₁⟩ := Fintype.card_pos_iff.mp ((congr_arg _ Nat.card_eq_fintype_card).mp (h₂ l₁))
      by_cases hl₂ : p in l₂
      · exact ⟨p, hl₁, hl₂⟩
      have key' : Fintype.card { q : P // q in l₂ } = Fintype.card { l : L // p in l } :=
        ((HasLines.lineCount_eq_pointCount h hl₂).trans Nat.card_eq_fintype_card).symm.trans
          Nat.card_eq_fintype_card
      have : forall q : { q // q in l₂ }, p != q := fun q hq => hl₂ ((congr_arg (· in l₂) hq).mpr q.2)
      let f : { q : P // q in l₂ } -> { l : L // p in l } := fun q =>
        ⟨mkLine (this q), (mkLine_ax (this q)).1⟩
      have hf : Function.Injective f := fun q₁ q₂ hq =>
        Subtype.ext ((eq_or_eq q₁.2 q₂.2 (mkLine_ax (this q₁)).2
            ((congr_arg (_ in ·) (Subtype.ext_iff.mp hq)).mpr (mkLine_ax (this q₂)).2)).resolve_right
            fun h => (congr_arg (p ∉ ·) h).mp hl₂ (mkLine_ax (this q₁)).1)
      have key' := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, key'⟩).2
      obtain ⟨q, hq⟩ := key' ⟨l₁, hl₁⟩
      exact ⟨q, (congr_arg (_ in ·) (Subtype.ext_iff.mp hq)).mp (mkLine_ax (this q)).2, q.2⟩
  { ‹HasLines P L› with
    mkPoint := fun {l₁ l₂} hl => Classical.choose (this l₁ l₂ hl)
    mkPoint_ax := fun {l₁ l₂} hl => Classical.choose_spec (this l₁ l₂ hl) }

/-- If a nondegenerate configuration has a unique point on any two lines, and if `|P| = |L|`,
  then there is a unique line through any two points. -/
@[instance_reducible]
/--
Definition of `HasPoints.hasLines` / `HasPoints.hasLines` 的定义

English:
definition HasPoints.hasLines
  signature: [HasPoints P L] [Fintype P] [Fintype L]
  body: let := @HasLines.hasPoints (Dual L) (Dual P) _ _ _ _ h.symm
  { ‹HasPoints P L› with
    mkLine := @fun _ _ => this.mkPoint
    mkLine_ax := @fun _ _ => this.mkPoint_ax }

中文:
定义 HasPoints.hasLines
  签名: [HasPoints P L] [Fintype P] [Fintype L]
  定义体: let := @HasLines.hasPoints (Dual L) (Dual P) _ _ _ _ h.symm
  { ‹HasPoints P L› with
    mkLine := @fun _ _ => this.mkPoint
    mkLine_ax := @fun _ _ => this.mkPoint_ax }

Depends on / 依赖: HasLines, HasLines.hasPoints, HasPoints, h.symm, hasPoints, mkLine, mkLine_ax, mkPoint, mkPoint_ax, this.mkPoint, this.mkPoint_ax
-/
noncomputable def HasPoints.hasLines [HasPoints P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) : HasLines P L :=
  let := @HasLines.hasPoints (Dual L) (Dual P) _ _ _ _ h.symm
  { ‹HasPoints P L› with
    mkLine := @fun _ _ => this.mkPoint
    mkLine_ax := @fun _ _ => this.mkPoint_ax }

variable (P L)

/--
Definition of `ProjectivePlane` / `ProjectivePlane` 的定义

English:
class ProjectivePlane
  parameters: extends HasPoints P L, HasLines P L
  extends: HasPoints P L, HasLines P L
  axioms and operations (1):
    - exists_config : exists (p₁ p₂ p₃ : P) (l₁ l₂ l₃ : L), p₁ ∉ l₂ ∧ p₁ ∉ l₃ ∧ p₂ ∉ l₁ ∧ p₂ in l₂ ∧ p₂ in l₃ ∧ p₃ ∉ l₁ ∧ p₃ in l₂ ∧ p₃ ∉ l₃

中文:
类 ProjectivePlane
  参数: extends HasPoints P L, HasLines P L
  继承: HasPoints P L, HasLines P L
  公理与运算 (1 个):
    - exists_config : 存在 (p₁ p₂ p₃ : P) (l₁ l₂ l₃ : L), p₁ ∉ l₂ ∧ p₁ ∉ l₃ ∧ p₂ ∉ l₁ ∧ p₂ in l₂ ∧ p₂ in l₃ ∧ p₃ ∉ l₁ ∧ p₃ in l₂ ∧ p₃ ∉ l₃

Depends on / 依赖: ListBlank, ListBlank.cons_head_tail, cons_head_tail
-/
class ProjectivePlane extends HasPoints P L, HasLines P L where
  exists_config :
    exists (p₁ p₂ p₃ : P) (l₁ l₂ l₃ : L),
      p₁ ∉ l₂ ∧ p₁ ∉ l₃ ∧ p₂ ∉ l₁ ∧ p₂ in l₂ ∧ p₂ in l₃ ∧ p₃ ∉ l₁ ∧ p₃ in l₂ ∧ p₃ ∉ l₃

namespace ProjectivePlane

variable [ProjectivePlane P L]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ProjectivePlane (Dual L) (Dual P)
  body: { Dual.hasPoints _ _, Dual.hasLines _ _ with
    exists_config :=
      let ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
      ⟨l₁, l₂, l₃, p₁, p₂, p₃, h₂₁, h₃₁, h₁₂, h₂₂, h₃₂, h₁₃, h₂₃, h₃₃⟩ }

中文:
实例 :
  签名: ProjectivePlane (Dual L) (Dual P)
  定义体: { Dual.hasPoints _ _, Dual.hasLines _ _ with
    exists_config :=
      let ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
      ⟨l₁, l₂, l₃, p₁, p₂, p₃, h₂₁, h₃₁, h₁₂, h₂₂, h₃₂, h₁₃, h₂₃, h₃₃⟩ }

Depends on / 依赖: Dual.hasLines, Dual.hasPoints, ListBlank, ListBlank.head_cons, ListBlank.tail_cons, Tape.mk, Tape.right, exists_config, hasLines, hasPoints, head_cons, tail_cons
-/
instance : ProjectivePlane (Dual L) (Dual P) :=
  { Dual.hasPoints _ _, Dual.hasLines _ _ with
    exists_config :=
      let ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
      ⟨l₁, l₂, l₃, p₁, p₂, p₃, h₂₁, h₃₁, h₁₂, h₂₂, h₃₂, h₁₃, h₂₃, h₃₃⟩ }

/--
Definition of `order` / `order` 的定义

English:
definition order
  signature: : Nat
  body: lineCount L (Classical.choose (@exists_config P L _ _)) - 1

中文:
定义 order
  签名: : 自然数
  定义体: lineCount L (Classical.choose (@exists_config P L _ _)) - 1

Depends on / 依赖: Classical, Classical.choose, exists_config, lineCount
-/
noncomputable def order : Nat :=
  lineCount L (Classical.choose (@exists_config P L _ _)) - 1

/--
theorem `card_points_eq_card_lines` / 定理 `card_points_eq_card_lines`

English:
theorem card_points_eq_card_lines
  given: [Fintype P] [Fintype L]
  statement: Fintype.card P = Fintype.card L
  proof: le_antisymm (HasLines.card_le P L) (HasPoints.card_le P L)

中文:
定理 card_points_eq_card_lines
  条件: [Fintype P] [Fintype L]
  结论: Fintype.card P = Fintype.card L
  证明: le_antisymm (HasLines.card_le P L) (HasPoints.card_le P L)

Depends on / 依赖: HasLines, HasLines.card_le, HasPoints, HasPoints.card_le, card_le, le_antisymm
-/
theorem card_points_eq_card_lines [Fintype P] [Fintype L] : Fintype.card P = Fintype.card L :=
  le_antisymm (HasLines.card_le P L) (HasPoints.card_le P L)

variable {P}

/--
theorem `lineCount_eq_lineCount` / 定理 `lineCount_eq_lineCount`

English:
theorem lineCount_eq_lineCount
  given: [Finite P] [Finite L] (p q : P)
  statement: lineCount L p = lineCount L q
  proof: by
  cases nonempty_fintype P
  cases nonempty_fintype L
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
  have h := card_points_eq_card_lines P L
  let n := lineCount L p₂
  have hp₂ : lineCount L p₂ = n := rfl
  have hl₁ : pointCount P l₁ = n := 

中文:
定理 lineCount_eq_lineCount
  条件: [Finite P] [Finite L] (p q : P)
  结论: lineCount L p = lineCount L q
  证明: by
  cases nonempty_fintype P
  cases nonempty_fintype L
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
  have h := card_points_eq_card_lines P L
  let n := lineCount L p₂
  have hp₂ : lineCount L p₂ = n := rfl
  have hl₁ : pointCount P l₁ = n := 

Depends on / 依赖: HasLines, HasLines.lineCount_eq_pointCount, card_points_eq_card_lines, exists_config, lineCount, lineCount_eq_pointCount, nonempty_fintype, pointCount, symm.trans
-/
theorem lineCount_eq_lineCount [Finite P] [Finite L] (p q : P) : lineCount L p = lineCount L q := by
  cases nonempty_fintype P
  cases nonempty_fintype L
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
  have h := card_points_eq_card_lines P L
  let n := lineCount L p₂
  have hp₂ : lineCount L p₂ = n := rfl
  have hl₁ : pointCount P l₁ = n := (HasLines.lineCount_eq_pointCount h h₂₁).symm.trans hp₂
  have hp₃ : lineCount L p₃ = n := (HasLines.lineCount_eq_pointCount h h₃₁).trans hl₁
  have hl₃ : pointCount P l₃ = n := (HasLines.lineCount_eq_pointCount h h₃₃).symm.trans hp₃
  have hp₁ : lineCount L p₁ = n := (HasLines.lineCount_eq_pointCount h h₁₃).trans hl₃
  have hl₂ : pointCount P l₂ = n := (HasLines.lineCount_eq_pointCount h h₁₂).symm.trans hp₁
  suffices forall p : P, lineCount L p = n by exact (this p).trans (this q).symm
  refine fun p =>
    or_not.elim (fun h₂ => ?_) fun h₂ => (HasLines.lineCount_eq_pointCount h h₂).trans hl₂
  refine or_not.elim (fun h₃ => ?_) fun h₃ => (HasLines.lineCount_eq_pointCount h h₃).trans hl₃
  rw [(eq_or_eq h₂ h₂₂ h₃ h₂₃).resolve_right fun h =>
      h₃₃ ((congr_arg (p₃ in ·) h).mp h₃₂)]

variable (P) {L}

/--
theorem `pointCount_eq_pointCount` / 定理 `pointCount_eq_pointCount`

English:
theorem pointCount_eq_pointCount
  given: [Finite P] [Finite L] (l m : L)
  proof: by
  apply lineCount_eq_lineCount (Dual P)

中文:
定理 pointCount_eq_pointCount
  条件: [Finite P] [Finite L] (l m : L)
  证明: by
  apply lineCount_eq_lineCount (Dual P)

Depends on / 依赖: lineCount_eq_lineCount
-/
theorem pointCount_eq_pointCount [Finite P] [Finite L] (l m : L) :
    pointCount P l = pointCount P m := by
  apply lineCount_eq_lineCount (Dual P)

variable {P}

/--
theorem `lineCount_eq_pointCount` / 定理 `lineCount_eq_pointCount`

English:
theorem lineCount_eq_pointCount
  given: [Finite P] [Finite L] (p : P) (l : L)
  proof: Exists.elim (exists_point l) fun q hq =>
(lineCount_eq_lineCount L p q).trans by
      cases nonempty_fintype P
      cases nonempty_fintype L
      exact HasLines.lineCount_eq_pointCount (card_points_eq_card_lines P L) hq

中文:
定理 lineCount_eq_pointCount
  条件: [Finite P] [Finite L] (p : P) (l : L)
  证明: Exists.elim (exists_point l) fun q hq =>
(lineCount_eq_lineCount L p q).trans by
      cases nonempty_fintype P
      cases nonempty_fintype L
      exact HasLines.lineCount_eq_pointCount (card_points_eq_card_lines P L) hq

Depends on / 依赖: Exists, Exists.elim, HasLines, HasLines.lineCount_eq_pointCount, card_points_eq_card_lines, exists_point, lineCount_eq_lineCount, lineCount_eq_pointCount, nonempty_fintype
-/
theorem lineCount_eq_pointCount [Finite P] [Finite L] (p : P) (l : L) :
    lineCount L p = pointCount P l :=
  Exists.elim (exists_point l) fun q hq =>
(lineCount_eq_lineCount L p q).trans by
      cases nonempty_fintype P
      cases nonempty_fintype L
      exact HasLines.lineCount_eq_pointCount (card_points_eq_card_lines P L) hq

variable (P L)

/--
theorem `Dual.order` / 定理 `Dual.order`

English:
theorem Dual.order
  given: [Finite P] [Finite L]
  statement: order (Dual L) (Dual P) = order P L
  proof: congr_arg (fun n => n - 1) (lineCount_eq_pointCount _ _)

中文:
定理 Dual.order
  条件: [Finite P] [Finite L]
  结论: order (Dual L) (Dual P) = order P L
  证明: congr_arg (fun n => n - 1) (lineCount_eq_pointCount _ _)

Depends on / 依赖: congr_arg, lineCount_eq_pointCount
-/
theorem Dual.order [Finite P] [Finite L] : order (Dual L) (Dual P) = order P L :=
  congr_arg (fun n => n - 1) (lineCount_eq_pointCount _ _)

variable {P}

/--
theorem `lineCount_eq` / 定理 `lineCount_eq`

English:
theorem lineCount_eq
  given: [Finite P] [Finite L] (p : P)
  statement: lineCount L p = order P L + 1
  proof: by
  obtain ⟨q, -, -, l, -, -, -, -, h, -⟩ := Classical.choose_spec (@exists_config P L _ _)
  cases nonempty_fintype { l : L // q in l }
  rw [order]; rw [lineCount_eq_lineCount L p q]; rw [lineCount_eq_lineCount L (Classical.choose _) q]; rw [lineCount]; rw [Nat.card_eq_fintype_card]; rw [Nat.sub_

中文:
定理 lineCount_eq
  条件: [Finite P] [Finite L] (p : P)
  结论: lineCount L p = order P L + 1
  证明: by
  obtain ⟨q, -, -, l, -, -, -, -, h, -⟩ := Classical.choose_spec (@exists_config P L _ _)
  cases nonempty_fintype { l : L // q in l }
  rw [order]; rw [lineCount_eq_lineCount L p q]; rw [lineCount_eq_lineCount L (Classical.choose _) q]; rw [lineCount]; rw [Nat.card_eq_fintype_card]; rw [Nat.sub_

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Fintype, Fintype.card_pos_iff.mpr, Nat.card_eq_fintype_card, Nat.sub_add_cancel, card_eq_fintype_card, card_pos_iff, choose_spec, exists_config, lineCount, lineCount_eq_lineCount, nonempty_fintype, sub_add_cancel
-/
theorem lineCount_eq [Finite P] [Finite L] (p : P) : lineCount L p = order P L + 1 := by
  obtain ⟨q, -, -, l, -, -, -, -, h, -⟩ := Classical.choose_spec (@exists_config P L _ _)
  cases nonempty_fintype { l : L // q in l }
  rw [order]; rw [lineCount_eq_lineCount L p q]; rw [lineCount_eq_lineCount L (Classical.choose _) q]; rw [lineCount]; rw [Nat.card_eq_fintype_card]; rw [Nat.sub_add_cancel]
  exact Fintype.card_pos_iff.mpr ⟨⟨l, h⟩⟩

variable (P) {L}

/--
theorem `pointCount_eq` / 定理 `pointCount_eq`

English:
theorem pointCount_eq
  given: [Finite P] [Finite L] (l : L)
  statement: pointCount P l = order P L + 1
  proof: (lineCount_eq (Dual P) _).trans (congr_arg (fun n => n + 1) (Dual.order P L))

中文:
定理 pointCount_eq
  条件: [Finite P] [Finite L] (l : L)
  结论: pointCount P l = order P L + 1
  证明: (lineCount_eq (Dual P) _).trans (congr_arg (fun n => n + 1) (Dual.order P L))

Depends on / 依赖: Dual.order, Tape.mk, Tape.right, congr_arg, lineCount_eq
-/
theorem pointCount_eq [Finite P] [Finite L] (l : L) : pointCount P l = order P L + 1 :=
  (lineCount_eq (Dual P) _).trans (congr_arg (fun n => n + 1) (Dual.order P L))

variable (L)

/--
theorem `one_lt_order` / 定理 `one_lt_order`

English:
theorem one_lt_order
  given: [Finite P] [Finite L]
  statement: 1 < order P L
  proof: by
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, -, -, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
  cases nonempty_fintype { p : P // p in l₂ }
  rw [← add_lt_add_iff_right 1]; rw [← pointCount_eq _ l₂]; rw [pointCount]; rw [Nat.card_eq_fintype_card]; rw [Fintype.two_lt_card_iff]
  simp_rw [Ne, Sub

中文:
定理 one_lt_order
  条件: [Finite P] [Finite L]
  结论: 1 < order P L
  证明: by
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, -, -, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
  cases nonempty_fintype { p : P // p in l₂ }
  rw [← add_lt_add_iff_right 1]; rw [← pointCount_eq _ l₂]; rw [pointCount]; rw [Nat.card_eq_fintype_card]; rw [Fintype.two_lt_card_iff]
  simp_rw [Ne, Sub

Depends on / 依赖: Fintype, Fintype.two_lt_card_iff, Nat.card_eq_fintype_card, Subtype, Subtype.ext_iff, add_lt_add_iff_right, card_eq_fintype_card, congr_arg, exists_config, ext_iff, mkPoint, mkPoint_ax, ne_of_mem_of_not_mem, nonempty_fintype, pointCount, pointCount_eq, simp_rw, two_lt_card_iff
-/
theorem one_lt_order [Finite P] [Finite L] : 1 < order P L := by
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, -, -, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
  cases nonempty_fintype { p : P // p in l₂ }
  rw [← add_lt_add_iff_right 1]; rw [← pointCount_eq _ l₂]; rw [pointCount]; rw [Nat.card_eq_fintype_card]; rw [Fintype.two_lt_card_iff]
  simp_rw [Ne, Subtype.ext_iff]
  have h := mkPoint_ax (P := P) (L := L) fun h => h₂₁ ((congr_arg (p₂ in ·) h).mpr h₂₂)
  exact
    ⟨⟨mkPoint _, h.2⟩, ⟨p₂, h₂₂⟩, ⟨p₃, h₃₂⟩, ne_of_mem_of_not_mem h.1 h₂₁,
      ne_of_mem_of_not_mem h.1 h₃₁, ne_of_mem_of_not_mem h₂₃ h₃₃⟩

variable {P}

/--
theorem `two_lt_lineCount` / 定理 `two_lt_lineCount`

English:
theorem two_lt_lineCount
  given: [Finite P] [Finite L] (p : P)
  statement: 2 < lineCount L p
  proof: by
  simpa only [lineCount_eq L p, Nat.succ_lt_succ_iff] using one_lt_order P L

中文:
定理 two_lt_lineCount
  条件: [Finite P] [Finite L] (p : P)
  结论: 2 < lineCount L p
  证明: by
  simpa only [lineCount_eq L p, Nat.succ_lt_succ_iff] using one_lt_order P L

Depends on / 依赖: Nat.succ_lt_succ_iff, lineCount_eq, one_lt_order, succ_lt_succ_iff
-/
theorem two_lt_lineCount [Finite P] [Finite L] (p : P) : 2 < lineCount L p := by
  simpa only [lineCount_eq L p, Nat.succ_lt_succ_iff] using one_lt_order P L

variable (P) {L}

/--
theorem `two_lt_pointCount` / 定理 `two_lt_pointCount`

English:
theorem two_lt_pointCount
  given: [Finite P] [Finite L] (l : L)
  statement: 2 < pointCount P l
  proof: by
  simpa only [pointCount_eq P l, Nat.succ_lt_succ_iff] using one_lt_order P L

中文:
定理 two_lt_pointCount
  条件: [Finite P] [Finite L] (l : L)
  结论: 2 < pointCount P l
  证明: by
  simpa only [pointCount_eq P l, Nat.succ_lt_succ_iff] using one_lt_order P L

Depends on / 依赖: Nat.succ_lt_succ_iff, one_lt_order, pointCount_eq, succ_lt_succ_iff
-/
theorem two_lt_pointCount [Finite P] [Finite L] (l : L) : 2 < pointCount P l := by
  simpa only [pointCount_eq P l, Nat.succ_lt_succ_iff] using one_lt_order P L

variable (L)

/--
theorem `card_points` / 定理 `card_points`

English:
theorem card_points
  given: [Fintype P] [Finite L]
  statement: Fintype.card P = order P L ^ 2 + order P L + 1
  proof: by
  cases nonempty_fintype L
  obtain ⟨p, -⟩ := @exists_config P L _ _
  let ϕ : { q // q != p } ≃ Σ l : { l : L // p in l }, { q // q in l.1 ∧ q != p } :=
    { toFun := fun q => ⟨⟨mkLine q.2, (mkLine_ax q.2).2⟩, q, (mkLine_ax q.2).1, q.2⟩
      invFun := fun lq => ⟨lq.2, lq.2.2.2⟩
      right_inv

中文:
定理 card_points
  条件: [Fintype P] [Finite L]
  结论: Fintype.card P = order P L ^ 2 + order P L + 1
  证明: by
  cases nonempty_fintype L
  obtain ⟨p, -⟩ := @exists_config P L _ _
  let ϕ : { q // q != p } ≃ Σ l : { l : L // p in l }, { q // q in l.1 ∧ q != p } :=
    { toFun := fun q => ⟨⟨mkLine q.2, (mkLine_ax q.2).2⟩, q, (mkLine_ax q.2).1, q.2⟩
      invFun := fun lq => ⟨lq.2, lq.2.2.2⟩
      right_inv

Depends on / 依赖: Fintype, Fintype.card, Sigma.subtype_ext, Subtype, Subtype.ext, classical, eq_or_eq, exists_config, invFun, mkLine, mkLine_ax, nonempty_fintype, resolve_left, right_inv, subtype_ext
-/
theorem card_points [Fintype P] [Finite L] : Fintype.card P = order P L ^ 2 + order P L + 1 := by
  cases nonempty_fintype L
  obtain ⟨p, -⟩ := @exists_config P L _ _
  let ϕ : { q // q != p } ≃ Σ l : { l : L // p in l }, { q // q in l.1 ∧ q != p } :=
    { toFun := fun q => ⟨⟨mkLine q.2, (mkLine_ax q.2).2⟩, q, (mkLine_ax q.2).1, q.2⟩
      invFun := fun lq => ⟨lq.2, lq.2.2.2⟩
      right_inv := fun lq =>
        Sigma.subtype_ext
          (Subtype.ext
            ((eq_or_eq (mkLine_ax lq.2.2.2).1 (mkLine_ax lq.2.2.2).2 lq.2.2.1 lq.1.2).resolve_left
              lq.2.2.2))
          rfl }
  classical
    have h1 : Fintype.card { q // q != p } + 1 = Fintype.card P := by
      apply (eq_tsub_iff_add_eq_of_le (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨p⟩))).mp
      convert! (Fintype.card_subtype_compl _).trans (congr_arg _ (Fintype.card_subtype_eq p))
    have h2 : forall l : { l : L // p in l }, Fintype.card { q // q in l.1 ∧ q != p } = order P L := by
      intro l
      rw [← Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· in l.val) (· != p))]; rw [Fintype.card_subtype_compl fun x : Subtype (· in l.val) => x.val = p]; rw [←
        Nat.card_eq_fintype_card]
      refine tsub_eq_of_eq_add ((pointCount_eq P l.1).trans ?_)
      rw [← Fintype.card_subtype_eq (⟨p]; rw [l.2⟩ : { q : P // q in l.1 })]
      simp_rw [Subtype.ext_iff]
    simp_rw [← h1, Fintype.card_congr ϕ, Fintype.card_sigma, h2, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card]; rw [← lineCount]; rw [lineCount_eq]; rw [smul_eq_mul]; rw [Nat.succ_mul]; rw [sq]

/--
theorem `card_lines` / 定理 `card_lines`

English:
theorem card_lines
  given: [Finite P] [Fintype L]
  statement: Fintype.card L = order P L ^ 2 + order P L + 1
  proof: (card_points (Dual L) (Dual P)).trans (congr_arg (fun n => n ^ 2 + n + 1) (Dual.order P L))

中文:
定理 card_lines
  条件: [Finite P] [Fintype L]
  结论: Fintype.card L = order P L ^ 2 + order P L + 1
  证明: (card_points (Dual L) (Dual P)).trans (congr_arg (fun n => n ^ 2 + n + 1) (Dual.order P L))

Depends on / 依赖: Dual.order, card_points, congr_arg
-/
theorem card_lines [Finite P] [Fintype L] : Fintype.card L = order P L ^ 2 + order P L + 1 :=
  (card_points (Dual L) (Dual P)).trans (congr_arg (fun n => n ^ 2 + n + 1) (Dual.order P L))

end ProjectivePlane

namespace ofField

variable {K : Type*} [Field K]

open scoped LinearAlgebra.Projectivization

open Matrix Projectivization

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership (ℙ K (Fin 3 -> K)) (ℙ K (Fin 3 -> K))
  body: ⟨Function.swap orthogonal⟩

中文:
实例 :
  签名: Membership (ℙ K (Fin 3 -> K)) (ℙ K (Fin 3 -> K))
  定义体: ⟨Function.swap orthogonal⟩

Depends on / 依赖: Function, Function.swap, orthogonal
-/
instance : Membership (ℙ K (Fin 3 -> K)) (ℙ K (Fin 3 -> K)) :=
  ⟨Function.swap orthogonal⟩

/--
lemma `mem_iff` / 引理 `mem_iff`

English:
lemma mem_iff
  given: (v w : ℙ K (Fin 3 -> K))
  statement: v in w ↔ orthogonal v w
  proof: Iff.rfl

中文:
引理 mem_iff
  条件: (v w : ℙ K (Fin 3 -> K))
  结论: v in w ↔ orthogonal v w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_iff (v w : ℙ K (Fin 3 -> K)) : v in w ↔ orthogonal v w :=
  Iff.rfl

-- This lemma can't be moved to the crossProduct file due to heavy imports
/--
lemma `crossProduct_eq_zero_of_dotProduct_eq_zero` / 引理 `crossProduct_eq_zero_of_dotProduct_eq_zero`

English:
lemma crossProduct_eq_zero_of_dotProduct_eq_zero
  statement: {a b c d : Fin 3 -> K} (hac : a ⬝ᵥ c = 0)
  proof: by
  by_contra h
  simp_rw [not_or, ← ne_eq, crossProduct_ne_zero_iff_linearIndependent] at h
  rw [← Matrix.of_row (![a]; rw [b]), ← Matrix.of_row (![c, d])] at h
  let A : Matrix (Fin 2) (Fin 3) K := .of ![a, b]
  let B : Matrix (Fin 2) (Fin 3) K := .of ![c, d]
  have hAB : A * B.transpose = 0 := 

中文:
引理 crossProduct_eq_zero_of_dotProduct_eq_zero
  结论: {a b c d : Fin 3 -> K} (hac : a ⬝ᵥ c = 0)
  证明: by
  by_contra h
  simp_rw [not_or, ← ne_eq, crossProduct_ne_zero_iff_linearIndependent] at h
  rw [← Matrix.of_row (![a]; rw [b]), ← Matrix.of_row (![c, d])] at h
  let A : Matrix (Fin 2) (Fin 3) K := .of ![a, b]
  let B : Matrix (Fin 2) (Fin 3) K := .of ![c, d]
  have hAB : A * B.transpose = 0 := 

Depends on / 依赖: B.transpose, Fintype, Fintype.ca, Fintype.card_fin, Matrix, Matrix.of_row, card_fin, crossProduct_ne_zero_iff_linearIndependent, fin_cases, ne_eq, not_or, of_row, rank_add_rank_le_card_of_mul_eq_zero, rank_matrix, rank_transpose, replace, simp_rw, transpose
-/
lemma crossProduct_eq_zero_of_dotProduct_eq_zero {a b c d : Fin 3 -> K} (hac : a ⬝ᵥ c = 0)
    (hbc : b ⬝ᵥ c = 0) (had : a ⬝ᵥ d = 0) (hbd : b ⬝ᵥ d = 0) :
    crossProduct a b = 0 ∨ crossProduct c d = 0 := by
  by_contra h
  simp_rw [not_or, ← ne_eq, crossProduct_ne_zero_iff_linearIndependent] at h
  rw [← Matrix.of_row (![a]; rw [b]), ← Matrix.of_row (![c, d])] at h
  let A : Matrix (Fin 2) (Fin 3) K := .of ![a, b]
  let B : Matrix (Fin 2) (Fin 3) K := .of ![c, d]
  have hAB : A * B.transpose = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> assumption
  replace hAB := rank_add_rank_le_card_of_mul_eq_zero hAB
  rw [rank_transpose]; rw [h.1.rank_matrix]; rw [h.2.rank_matrix]; rw [Fintype.card_fin]; rw [Fintype.card_fin] at hAB
  contradiction

/--
lemma `eq_or_eq_of_orthogonal` / 引理 `eq_or_eq_of_orthogonal`

English:
lemma eq_or_eq_of_orthogonal
  statement: {a b c d : ℙ K (Fin 3 -> K)} (hac : a.orthogonal c)
  proof: by
  induction a with | h a ha =>
  induction b with | h b hb =>
  induction c with | h c hc =>
  induction d with | h d hd =>
  rw [mk_eq_mk_iff_crossProduct_eq_zero]; rw [mk_eq_mk_iff_crossProduct_eq_zero]
  exact crossProduct_eq_zero_of_dotProduct_eq_zero hac hbc had hbd

中文:
引理 eq_or_eq_of_orthogonal
  结论: {a b c d : ℙ K (Fin 3 -> K)} (hac : a.orthogonal c)
  证明: by
  induction a with | h a ha =>
  induction b with | h b hb =>
  induction c with | h c hc =>
  induction d with | h d hd =>
  rw [mk_eq_mk_iff_crossProduct_eq_zero]; rw [mk_eq_mk_iff_crossProduct_eq_zero]
  exact crossProduct_eq_zero_of_dotProduct_eq_zero hac hbc had hbd

Depends on / 依赖: crossProduct_eq_zero_of_dotProduct_eq_zero, mk_eq_mk_iff_crossProduct_eq_zero
-/
lemma eq_or_eq_of_orthogonal {a b c d : ℙ K (Fin 3 -> K)} (hac : a.orthogonal c)
    (hbc : b.orthogonal c) (had : a.orthogonal d) (hbd : b.orthogonal d) :
    a = b ∨ c = d := by
  induction a with | h a ha =>
  induction b with | h b hb =>
  induction c with | h c hc =>
  induction d with | h d hd =>
  rw [mk_eq_mk_iff_crossProduct_eq_zero]; rw [mk_eq_mk_iff_crossProduct_eq_zero]
  exact crossProduct_eq_zero_of_dotProduct_eq_zero hac hbc had hbd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nondegenerate (ℙ K (Fin 3 -> K)) (ℙ K (Fin 3 -> K))
  body: { exists_point := exists_not_orthogonal_self
    exists_line := exists_not_self_orthogonal
    eq_or_eq := eq_or_eq_of_orthogonal }

中文:
实例 :
  签名: Nondegenerate (ℙ K (Fin 3 -> K)) (ℙ K (Fin 3 -> K))
  定义体: { exists_point := exists_not_orthogonal_self
    exists_line := exists_not_self_orthogonal
    eq_or_eq := eq_or_eq_of_orthogonal }

Depends on / 依赖: eq_or_eq, eq_or_eq_of_orthogonal, exists_line, exists_not_orthogonal_self, exists_not_self_orthogonal, exists_point
-/
instance : Nondegenerate (ℙ K (Fin 3 -> K)) (ℙ K (Fin 3 -> K)) :=
  { exists_point := exists_not_orthogonal_self
    exists_line := exists_not_self_orthogonal
    eq_or_eq := eq_or_eq_of_orthogonal }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: K] : ProjectivePlane (ℙ K (Fin 3 -> K)) (ℙ K (Fin 3 -> K))
  body: { mkPoint := by
      intro v w _
      exact cross v w
    mkPoint_ax := fun h => ⟨cross_orthogonal_left h, cross_orthogonal_right h⟩
    mkLine := by
      intro v w _
      exact cross v w
    mkLine_ax := fun h => ⟨orthogonal_cross_left h, orthogonal_cross_right h⟩
    exists_config := by
      

中文:
实例 [DecidableEq
  签名: K] : ProjectivePlane (ℙ K (Fin 3 -> K)) (ℙ K (Fin 3 -> K))
  定义体: { mkPoint := by
      intro v w _
      exact cross v w
    mkPoint_ax := fun h => ⟨cross_orthogonal_left h, cross_orthogonal_right h⟩
    mkLine := by
      intro v w _
      exact cross v w
    mkLine_ax := fun h => ⟨orthogonal_cross_left h, orthogonal_cross_right h⟩
    exists_config := by
      

Depends on / 依赖: cross_orthogonal_left, cross_orthogonal_right, exists_config, mem_iff, mkLine, mkLine_ax, mkPoint, mkPoint_ax, orthogonal_cross_left, orthogonal_cross_right, orthogonal_mk
-/
noncomputable instance [DecidableEq K] : ProjectivePlane (ℙ K (Fin 3 -> K)) (ℙ K (Fin 3 -> K)) :=
  { mkPoint := by
      intro v w _
      exact cross v w
    mkPoint_ax := fun h => ⟨cross_orthogonal_left h, cross_orthogonal_right h⟩
    mkLine := by
      intro v w _
      exact cross v w
    mkLine_ax := fun h => ⟨orthogonal_cross_left h, orthogonal_cross_right h⟩
    exists_config := by
      refine ⟨mk K ![0, 1, 1] ?_, mk K ![1, 0, 0] ?_, mk K ![1, 0, 1] ?_, mk K ![1, 0, 0] ?_,
        mk K ![0, 1, 0] ?_, mk K ![0, 0, 1] ?_, ?_⟩ <;> simp [mem_iff, orthogonal_mk] }

end ofField

end Configuration
