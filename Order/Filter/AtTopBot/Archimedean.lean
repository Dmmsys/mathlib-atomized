/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.Tactic.GCongr
import Mathlib.Algebra.Order.Group.Basic

/-!
# `Filter.atTop` filter and archimedean (semi)rings/fields

In this file we prove that for a linear ordered archimedean semiring `R` and a function `f : α → ℕ`,
the function `Nat.cast ∘ f : α → R` tends to `Filter.atTop` along a filter `l` if and only if so
does `f`. We also prove that `Nat.cast : ℕ → R` tends to `Filter.atTop` along `Filter.atTop`, as
well as version of these two results for `ℤ` (and a ring `R`) and `ℚ` (and a field `R`).
-/

public section


variable {α R : Type*}

open Filter Set Function

@[simp]
/--
theorem `Nat.comap_cast_atTop` / 定理 `Nat.comap_cast_atTop`

English:
theorem Nat.comap_cast_atTop
  given: [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]
  proof: comap_embedding_atTop (fun _ _ => Nat.cast_le) exists_nat_ge

中文:
定理 自然数.comap_cast_atTop
  条件: [半环 R] [偏序 R] [是StrictOrdered环 R] [阿基米德 R]
  证明: comap_embedding_atTop (fun _ _ => Nat.cast_le) exists_nat_ge

Depends on / 依赖: Nat.cast_le, cast_le, comap_embedding_atTop, exists_nat_ge
-/
theorem Nat.comap_cast_atTop [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] :
    comap ((↑) : Nat -> R) atTop = atTop :=
  comap_embedding_atTop (fun _ _ => Nat.cast_le) exists_nat_ge

/--
theorem `tendsto_natCast_atTop_iff` / 定理 `tendsto_natCast_atTop_iff`

English:
theorem tendsto_natCast_atTop_iff
  statement: [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  proof: tendsto_atTop_embedding (fun _ _ => Nat.cast_le) exists_nat_ge

中文:
定理 tendsto_natCast_atTop_iff
  结论: [半环 R] [偏序 R] [是StrictOrdered环 R]
  证明: tendsto_atTop_embedding (fun _ _ => Nat.cast_le) exists_nat_ge

Depends on / 依赖: Nat.cast_le, cast_le, exists_nat_ge, tendsto_atTop_embedding
-/
theorem tendsto_natCast_atTop_iff [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {f : α -> Nat}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atTop ↔ Tendsto f l atTop :=
  tendsto_atTop_embedding (fun _ _ => Nat.cast_le) exists_nat_ge

/--
theorem `PNat.tendsto_comp_val_iff` / 定理 `PNat.tendsto_comp_val_iff`

English:
theorem PNat.tendsto_comp_val_iff
  given: {β : Type*} {f : Nat -> β} {l : Filter β}
  proof: by
  exact tendsto_comp_val_Ioi_atTop

中文:
定理 正自然数.tendsto_comp_val_iff
  条件: {β : 类型} {f : 自然数 -> β} {l : 滤子 β}
  证明: by
  exact tendsto_comp_val_Ioi_atTop

Depends on / 依赖: tendsto_comp_val_Ioi_atTop
-/
theorem PNat.tendsto_comp_val_iff {β : Type*} {f : Nat -> β} {l : Filter β} :
    Tendsto (fun x : Nat+ => f x) atTop l ↔ Tendsto f atTop l := by
  exact tendsto_comp_val_Ioi_atTop

/--
theorem `tendsto_natCast_atTop_atTop` / 定理 `tendsto_natCast_atTop_atTop`

English:
theorem tendsto_natCast_atTop_atTop
  statement: [Semiring R] [PartialOrder R] [IsOrderedRing R]
  proof: Nat.mono_cast.tendsto_atTop_atTop exists_nat_ge

中文:
定理 tendsto_natCast_atTop_atTop
  结论: [半环 R] [偏序 R] [是Ordered环 R]
  证明: Nat.mono_cast.tendsto_atTop_atTop exists_nat_ge

Depends on / 依赖: Nat.mono_cast.tendsto_atTop_atTop, exists_nat_ge, mono_cast, tendsto_atTop_atTop
-/
theorem tendsto_natCast_atTop_atTop [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] :
    Tendsto ((↑) : Nat -> R) atTop atTop :=
  Nat.mono_cast.tendsto_atTop_atTop exists_nat_ge

/--
lemma `tendsto_PNat_val_atTop_atTop` / 引理 `tendsto_PNat_val_atTop_atTop`

English:
lemma tendsto_PNat_val_atTop_atTop
  statement: Tendsto PNat.val atTop atTop
  proof: tendsto_atTop_atTop_of_monotone (fun _ _ h => h) fun a => ⟨Nat.succPNat a, Nat.le_succ a⟩

中文:
引理 tendsto_P自然数_val_atTop_atTop
  结论: 收敛 正自然数.val atTop atTop
  证明: tendsto_atTop_atTop_of_monotone (fun _ _ h => h) fun a => ⟨Nat.succPNat a, Nat.le_succ a⟩

Depends on / 依赖: Nat.le_succ, Nat.succPNat, le_succ, succPNat, tendsto_atTop_atTop_of_monotone
-/
lemma tendsto_PNat_val_atTop_atTop : Tendsto PNat.val atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ h => h) fun a => ⟨Nat.succPNat a, Nat.le_succ a⟩

/--
theorem `Filter.Eventually.natCast_atTop` / 定理 `Filter.Eventually.natCast_atTop`

English:
theorem Filter.Eventually.natCast_atTop
  statement: [Semiring R] [PartialOrder R] [IsOrderedRing R]
  proof: tendsto_natCast_atTop_atTop.eventually h

中文:
定理 滤子.Eventually.natCast_atTop
  结论: [半环 R] [偏序 R] [是Ordered环 R]
  证明: tendsto_natCast_atTop_atTop.eventually h

Depends on / 依赖: eventually, tendsto_natCast_atTop_atTop, tendsto_natCast_atTop_atTop.eventually
-/
theorem Filter.Eventually.natCast_atTop [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] {p : R -> Prop}
    (h : forallᶠ (x : R) in atTop, p x) : forallᶠ (n : Nat) in atTop, p n :=
  tendsto_natCast_atTop_atTop.eventually h

/--
theorem `Int.comap_cast_atTop` / 定理 `Int.comap_cast_atTop`

English:
theorem Int.comap_cast_atTop
  statement: [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
  proof: comap_embedding_atTop (fun _ _ => Int.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r; ⟨n, mod_cast hn⟩

@[simp]

中文:
定理 整数.comap_cast_atTop
  结论: [环 R] [偏序 R] [是StrictOrdered环 R]
  证明: comap_embedding_atTop (fun _ _ => Int.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r; ⟨n, mod_cast hn⟩

@[simp]
-/
@[simp] theorem Int.comap_cast_atTop [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] :
    comap ((↑) : Int -> R) atTop = atTop :=
  comap_embedding_atTop (fun _ _ => Int.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r; ⟨n, mod_cast hn⟩

@[simp]
/--
theorem `Int.comap_cast_atBot` / 定理 `Int.comap_cast_atBot`

English:
theorem Int.comap_cast_atBot
  given: [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]
  proof: comap_embedding_atBot (fun _ _ => Int.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by simpa [neg_le] using hn⟩

中文:
定理 整数.comap_cast_atBot
  条件: [环 R] [偏序 R] [是StrictOrdered环 R] [阿基米德 R]
  证明: comap_embedding_atBot (fun _ _ => Int.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by simpa [neg_le] using hn⟩

Depends on / 依赖: Int.cast_le, cast_le, comap_embedding_atBot, exists_nat_ge, neg_le
-/
theorem Int.comap_cast_atBot [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] :
    comap ((↑) : Int -> R) atBot = atBot :=
  comap_embedding_atBot (fun _ _ => Int.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by simpa [neg_le] using hn⟩

/--
theorem `tendsto_intCast_atTop_iff` / 定理 `tendsto_intCast_atTop_iff`

English:
theorem tendsto_intCast_atTop_iff
  statement: [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]
  proof: by
  rw [← @Int.comap_cast_atTop R]; rw [tendsto_comap_iff]; rfl

中文:
定理 tendsto_intCast_atTop_iff
  结论: [环 R] [偏序 R] [是StrictOrdered环 R] [阿基米德 R]
  证明: by
  rw [← @Int.comap_cast_atTop R]; rw [tendsto_comap_iff]; rfl

Depends on / 依赖: Int.comap_cast_atTop, comap_cast_atTop, tendsto_comap_iff
-/
theorem tendsto_intCast_atTop_iff [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]
    {f : α -> Int}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atTop ↔ Tendsto f l atTop := by
  rw [← @Int.comap_cast_atTop R]; rw [tendsto_comap_iff]; rfl

/--
theorem `tendsto_intCast_atBot_iff` / 定理 `tendsto_intCast_atBot_iff`

English:
theorem tendsto_intCast_atBot_iff
  statement: [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
  proof: by
  rw [← @Int.comap_cast_atBot R]; rw [tendsto_comap_iff]; rfl

中文:
定理 tendsto_intCast_atBot_iff
  结论: [环 R] [偏序 R] [是StrictOrdered环 R]
  证明: by
  rw [← @Int.comap_cast_atBot R]; rw [tendsto_comap_iff]; rfl

Depends on / 依赖: Int.comap_cast_atBot, comap_cast_atBot, tendsto_comap_iff
-/
theorem tendsto_intCast_atBot_iff [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {f : α -> Int}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atBot ↔ Tendsto f l atBot := by
  rw [← @Int.comap_cast_atBot R]; rw [tendsto_comap_iff]; rfl

/--
theorem `tendsto_intCast_atTop_atTop` / 定理 `tendsto_intCast_atTop_atTop`

English:
theorem tendsto_intCast_atTop_atTop
  statement: [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
  proof: tendsto_intCast_atTop_iff.2 tendsto_id

中文:
定理 tendsto_intCast_atTop_atTop
  结论: [环 R] [偏序 R] [是StrictOrdered环 R]
  证明: tendsto_intCast_atTop_iff.2 tendsto_id

Depends on / 依赖: tendsto_id, tendsto_intCast_atTop_iff
-/
theorem tendsto_intCast_atTop_atTop [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] :
    Tendsto ((↑) : Int -> R) atTop atTop :=
  tendsto_intCast_atTop_iff.2 tendsto_id

/--
theorem `Filter.Eventually.intCast_atTop` / 定理 `Filter.Eventually.intCast_atTop`

English:
theorem Filter.Eventually.intCast_atTop
  statement: [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
  proof: by
  rw [← Int.comap_cast_atTop (R := R)]; exact h.comap _

中文:
定理 滤子.Eventually.intCast_atTop
  结论: [环 R] [偏序 R] [是StrictOrdered环 R]
  证明: by
  rw [← Int.comap_cast_atTop (R := R)]; exact h.comap _

Depends on / 依赖: Int.comap_cast_atTop, comap_cast_atTop, h.comap
-/
theorem Filter.Eventually.intCast_atTop [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {p : R -> Prop}
    (h : forallᶠ (x : R) in atTop, p x) : forallᶠ (n : Int) in atTop, p n := by
  rw [← Int.comap_cast_atTop (R := R)]; exact h.comap _

/--
theorem `Filter.Eventually.intCast_atBot` / 定理 `Filter.Eventually.intCast_atBot`

English:
theorem Filter.Eventually.intCast_atBot
  statement: [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
  proof: by
  rw [← Int.comap_cast_atBot (R := R)]; exact h.comap _

@[simp]

中文:
定理 滤子.Eventually.intCast_atBot
  结论: [环 R] [偏序 R] [是StrictOrdered环 R]
  证明: by
  rw [← Int.comap_cast_atBot (R := R)]; exact h.comap _

@[simp]

Depends on / 依赖: Int.comap_cast_atBot, comap_cast_atBot, h.comap
-/
theorem Filter.Eventually.intCast_atBot [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {p : R -> Prop}
    (h : forallᶠ (x : R) in atBot, p x) : forallᶠ (n : Int) in atBot, p n := by
  rw [← Int.comap_cast_atBot (R := R)]; exact h.comap _

@[simp]
/--
theorem `Rat.comap_cast_atTop` / 定理 `Rat.comap_cast_atTop`

English:
theorem Rat.comap_cast_atTop
  given: [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R]
  proof: comap_embedding_atTop (fun _ _ => Rat.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r; ⟨n, by simpa⟩

中文:
定理 有理数.comap_cast_atTop
  条件: [域 R] [线性序 R] [是StrictOrdered环 R] [阿基米德 R]
  证明: comap_embedding_atTop (fun _ _ => Rat.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r; ⟨n, by simpa⟩

Depends on / 依赖: Rat.cast_le, cast_le, comap_embedding_atTop, exists_nat_ge
-/
theorem Rat.comap_cast_atTop [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R] :
    comap ((↑) : Rat -> R) atTop = atTop :=
  comap_embedding_atTop (fun _ _ => Rat.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r; ⟨n, by simpa⟩

/--
theorem `Rat.comap_cast_atBot` / 定理 `Rat.comap_cast_atBot`

English:
theorem Rat.comap_cast_atBot
  statement: [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: comap_embedding_atBot (fun _ _ => Rat.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by simpa [neg_le]⟩

中文:
定理 有理数.comap_cast_atBot
  结论: [域 R] [线性序 R] [是StrictOrdered环 R]
  证明: comap_embedding_atBot (fun _ _ => Rat.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by simpa [neg_le]⟩
-/
@[simp] theorem Rat.comap_cast_atBot [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] :
    comap ((↑) : Rat -> R) atBot = atBot :=
  comap_embedding_atBot (fun _ _ => Rat.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by simpa [neg_le]⟩

/--
theorem `tendsto_ratCast_atTop_iff` / 定理 `tendsto_ratCast_atTop_iff`

English:
theorem tendsto_ratCast_atTop_iff
  statement: [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R]
  proof: by
  rw [← @Rat.comap_cast_atTop R]; rw [tendsto_comap_iff]; rfl

中文:
定理 tendsto_ratCast_atTop_iff
  结论: [域 R] [线性序 R] [是StrictOrdered环 R] [阿基米德 R]
  证明: by
  rw [← @Rat.comap_cast_atTop R]; rw [tendsto_comap_iff]; rfl

Depends on / 依赖: Rat.comap_cast_atTop, comap_cast_atTop, tendsto_comap_iff
-/
theorem tendsto_ratCast_atTop_iff [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R]
    {f : α -> Rat}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atTop ↔ Tendsto f l atTop := by
  rw [← @Rat.comap_cast_atTop R]; rw [tendsto_comap_iff]; rfl

/--
theorem `tendsto_ratCast_atBot_iff` / 定理 `tendsto_ratCast_atBot_iff`

English:
theorem tendsto_ratCast_atBot_iff
  statement: [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  rw [← @Rat.comap_cast_atBot R]; rw [tendsto_comap_iff]; rfl

中文:
定理 tendsto_ratCast_atBot_iff
  结论: [域 R] [线性序 R] [是StrictOrdered环 R]
  证明: by
  rw [← @Rat.comap_cast_atBot R]; rw [tendsto_comap_iff]; rfl

Depends on / 依赖: Rat.comap_cast_atBot, comap_cast_atBot, tendsto_comap_iff
-/
theorem tendsto_ratCast_atBot_iff [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {f : α -> Rat}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atBot ↔ Tendsto f l atBot := by
  rw [← @Rat.comap_cast_atBot R]; rw [tendsto_comap_iff]; rfl

/--
theorem `Filter.Eventually.ratCast_atTop` / 定理 `Filter.Eventually.ratCast_atTop`

English:
theorem Filter.Eventually.ratCast_atTop
  statement: [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  rw [← Rat.comap_cast_atTop (R := R)]; exact h.comap _

中文:
定理 滤子.Eventually.ratCast_atTop
  结论: [域 R] [线性序 R] [是StrictOrdered环 R]
  证明: by
  rw [← Rat.comap_cast_atTop (R := R)]; exact h.comap _

Depends on / 依赖: Rat.comap_cast_atTop, comap_cast_atTop, h.comap
-/
theorem Filter.Eventually.ratCast_atTop [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {p : R -> Prop}
    (h : forallᶠ (x : R) in atTop, p x) : forallᶠ (n : Rat) in atTop, p n := by
  rw [← Rat.comap_cast_atTop (R := R)]; exact h.comap _

/--
theorem `Filter.Eventually.ratCast_atBot` / 定理 `Filter.Eventually.ratCast_atBot`

English:
theorem Filter.Eventually.ratCast_atBot
  statement: [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  rw [← Rat.comap_cast_atBot (R := R)]; exact h.comap _

中文:
定理 滤子.Eventually.ratCast_atBot
  结论: [域 R] [线性序 R] [是StrictOrdered环 R]
  证明: by
  rw [← Rat.comap_cast_atBot (R := R)]; exact h.comap _

Depends on / 依赖: Rat.comap_cast_atBot, comap_cast_atBot, h.comap
-/
theorem Filter.Eventually.ratCast_atBot [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {p : R -> Prop}
    (h : forallᶠ (x : R) in atBot, p x) : forallᶠ (n : Rat) in atBot, p n := by
  rw [← Rat.comap_cast_atBot (R := R)]; exact h.comap _

/--
theorem `atTop_hasAntitoneBasis_of_archimedean` / 定理 `atTop_hasAntitoneBasis_of_archimedean`

English:
theorem atTop_hasAntitoneBasis_of_archimedean
  statement: [Semiring R] [PartialOrder R] [IsOrderedRing R]
  proof: hasAntitoneBasis_atTop.comp_mono Nat.mono_cast tendsto_natCast_atTop_atTop

中文:
定理 atTop_hasAntitoneBasis_of_archimedean
  结论: [半环 R] [偏序 R] [是Ordered环 R]
  证明: hasAntitoneBasis_atTop.comp_mono Nat.mono_cast tendsto_natCast_atTop_atTop

Depends on / 依赖: Nat.mono_cast, comp_mono, hasAntitoneBasis_atTop, hasAntitoneBasis_atTop.comp_mono, mono_cast, tendsto_natCast_atTop_atTop
-/
theorem atTop_hasAntitoneBasis_of_archimedean [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] :
    (atTop : Filter R).HasAntitoneBasis fun n : Nat => Ici n :=
  hasAntitoneBasis_atTop.comp_mono Nat.mono_cast tendsto_natCast_atTop_atTop

/--
theorem `atTop_hasCountableBasis_of_archimedean` / 定理 `atTop_hasCountableBasis_of_archimedean`

English:
theorem atTop_hasCountableBasis_of_archimedean
  statement: [Semiring R] [PartialOrder R] [IsOrderedRing R]
  proof: ⟨atTop_hasAntitoneBasis_of_archimedean.1, to_countable _⟩

中文:
定理 atTop_hasCountableBasis_of_archimedean
  结论: [半环 R] [偏序 R] [是Ordered环 R]
  证明: ⟨atTop_hasAntitoneBasis_of_archimedean.1, to_countable _⟩

Depends on / 依赖: atTop_hasAntitoneBasis_of_archimedean, to_countable
-/
theorem atTop_hasCountableBasis_of_archimedean [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] :
    (atTop : Filter R).HasCountableBasis (fun _ : Nat => True) fun n => Ici n :=
  ⟨atTop_hasAntitoneBasis_of_archimedean.1, to_countable _⟩

/--
theorem `atBot_hasCountableBasis_of_archimedean` / 定理 `atBot_hasCountableBasis_of_archimedean`

English:
theorem atBot_hasCountableBasis_of_archimedean
  statement: [Ring R] [PartialOrder R] [IsOrderedRing R]
  proof: to_countable _
  toHasBasis :=
    atBot_basis.to_hasBasis
      (fun x _ => let ⟨m, hm⟩ := exists_int_le x; ⟨m, trivial, Iic_subset_Iic.2 hm⟩)
      fun m _ => ⟨m, trivial, Subset.rfl⟩

中文:
定理 atBot_hasCountableBasis_of_archimedean
  结论: [环 R] [偏序 R] [是Ordered环 R]
  证明: to_countable _
  toHasBasis :=
    atBot_basis.to_hasBasis
      (fun x _ => let ⟨m, hm⟩ := exists_int_le x; ⟨m, trivial, Iic_subset_Iic.2 hm⟩)
      fun m _ => ⟨m, trivial, Subset.rfl⟩

Depends on / 依赖: to_countable
-/
theorem atBot_hasCountableBasis_of_archimedean [Ring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] :
    (atBot : Filter R).HasCountableBasis (fun _ : Int => True) fun m => Iic m where
  countable := to_countable _
  toHasBasis :=
    atBot_basis.to_hasBasis
      (fun x _ => let ⟨m, hm⟩ := exists_int_le x; ⟨m, trivial, Iic_subset_Iic.2 hm⟩)
      fun m _ => ⟨m, trivial, Subset.rfl⟩

instance (priority := 100) atTop_isCountablyGenerated_of_archimedean
    [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] : (atTop : Filter R).IsCountablyGenerated :=
  atTop_hasCountableBasis_of_archimedean.isCountablyGenerated

instance (priority := 100) atBot_isCountablyGenerated_of_archimedean
    [Ring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] : (atBot : Filter R).IsCountablyGenerated :=
  atBot_hasCountableBasis_of_archimedean.isCountablyGenerated

namespace Filter

variable {l : Filter α} {f : α -> R} {r : R}

/--
theorem `map_add_atTop_eq` / 定理 `map_add_atTop_eq`

English:
theorem map_add_atTop_eq
  statement: [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  proof: map_atTop_eq_of_gc (fun a => a - k) 0 add_left_mono (by simp [le_sub_iff_add_le]) (by simp)

中文:
定理 map_add_atTop_eq
  结论: [加法交换群 α] [偏序 α] [是OrderedAdd幺半群 α]
  证明: map_atTop_eq_of_gc (fun a => a - k) 0 add_left_mono (by simp [le_sub_iff_add_le]) (by simp)

Depends on / 依赖: add_left_mono, le_sub_iff_add_le, map_atTop_eq_of_gc
-/
theorem map_add_atTop_eq [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    [IsDirectedOrder α] (k : α) : map (fun a => a + k) atTop = atTop :=
  map_atTop_eq_of_gc (fun a => a - k) 0 add_left_mono (by simp [le_sub_iff_add_le]) (by simp)

/--
theorem `map_sub_atTop_eq` / 定理 `map_sub_atTop_eq`

English:
theorem map_sub_atTop_eq
  statement: [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  proof: by
  simp_rw [sub_eq_add_neg]
  apply map_add_atTop_eq

中文:
定理 map_sub_atTop_eq
  结论: [加法交换群 α] [偏序 α] [是OrderedAdd幺半群 α]
  证明: by
  simp_rw [sub_eq_add_neg]
  apply map_add_atTop_eq

Depends on / 依赖: map_add_atTop_eq, simp_rw, sub_eq_add_neg
-/
theorem map_sub_atTop_eq [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    [IsDirectedOrder α] (k : α) : map (fun a => a - k) atTop = atTop := by
  simp_rw [sub_eq_add_neg]
  apply map_add_atTop_eq

section LinearOrderedSemiring

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R]

/--
theorem `Tendsto.const_mul_atTop'` / 定理 `Tendsto.const_mul_atTop'`

English:
theorem Tendsto.const_mul_atTop'
  given: (hr : 0 < r) (hf : Tendsto f l atTop)
  proof: by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨n : Nat, hn : 1 <= n • r⟩ := Archimedean.arch 1 hr
  rw [nsmul_eq_mul'] at hn
  filter_upwards [tendsto_atTop.1 hf (n * max b 0)] with x hx
  calc
    b <= 1 * max b 0 := by
    { rw [one_mul]
      exact le_max_left _ _ }
    _ <= r * n * max b 0 :=

中文:
定理 收敛.const_mul_atTop'
  条件: (hr : 0 < r) (hf : 收敛 f l atTop)
  证明: by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨n : Nat, hn : 1 <= n • r⟩ := Archimedean.arch 1 hr
  rw [nsmul_eq_mul'] at hn
  filter_upwards [tendsto_atTop.1 hf (n * max b 0)] with x hx
  calc
    b <= 1 * max b 0 := by
    { rw [one_mul]
      exact le_max_left _ _ }
    _ <= r * n * max b 0 :=

Depends on / 依赖: Archimedean, Archimedean.arch, filter_upwards, le_max_left, mul_assoc, nsmul_eq_mul, one_mul, tendsto_atTop
-/
theorem Tendsto.const_mul_atTop' (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atTop := by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨n : Nat, hn : 1 <= n • r⟩ := Archimedean.arch 1 hr
  rw [nsmul_eq_mul'] at hn
  filter_upwards [tendsto_atTop.1 hf (n * max b 0)] with x hx
  calc
    b <= 1 * max b 0 := by
    { rw [one_mul]
      exact le_max_left _ _ }
    _ <= r * n * max b 0 := by gcongr
    _ = r * (n * max b 0) := by rw [mul_assoc]
    _ <= r * f x := by gcongr

/--
theorem `Tendsto.atTop_mul_const'` / 定理 `Tendsto.atTop_mul_const'`

English:
theorem Tendsto.atTop_mul_const'
  given: (hr : 0 < r) (hf : Tendsto f l atTop)
  proof: by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨n : Nat, hn : 1 <= n • r⟩ := Archimedean.arch 1 hr
  have hn' : 1 <= (n : R) * r := by rwa [nsmul_eq_mul] at hn
  filter_upwards [tendsto_atTop.1 hf (max b 0 * n)] with x hx
  calc
    b <= max b 0 * 1 := by
    { rw [mul_one]
      exact le_max_left

中文:
定理 收敛.atTop_mul_const'
  条件: (hr : 0 < r) (hf : 收敛 f l atTop)
  证明: by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨n : Nat, hn : 1 <= n • r⟩ := Archimedean.arch 1 hr
  have hn' : 1 <= (n : R) * r := by rwa [nsmul_eq_mul] at hn
  filter_upwards [tendsto_atTop.1 hf (max b 0 * n)] with x hx
  calc
    b <= max b 0 * 1 := by
    { rw [mul_one]
      exact le_max_left

Depends on / 依赖: Archimedean, Archimedean.arch, filter_upwards, le_max_left, mul_assoc, mul_one, nsmul_eq_mul, tendsto_atTop
-/
theorem Tendsto.atTop_mul_const' (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atTop := by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨n : Nat, hn : 1 <= n • r⟩ := Archimedean.arch 1 hr
  have hn' : 1 <= (n : R) * r := by rwa [nsmul_eq_mul] at hn
  filter_upwards [tendsto_atTop.1 hf (max b 0 * n)] with x hx
  calc
    b <= max b 0 * 1 := by
    { rw [mul_one]
      exact le_max_left _ _ }
    _ <= max b 0 * (n * r) := by gcongr
    _ = max b 0 * n * r := by rw [mul_assoc]
    _ <= f x * r := by gcongr

end LinearOrderedSemiring

section LinearOrderedRing

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R]

/--
theorem `Tendsto.atTop_mul_const_of_neg'` / 定理 `Tendsto.atTop_mul_const_of_neg'`

English:
theorem Tendsto.atTop_mul_const_of_neg'
  given: (hr : r < 0) (hf : Tendsto f l atTop)
  proof: by
  simpa only [tendsto_neg_atTop_iff, mul_neg] using hf.atTop_mul_const' (neg_pos.mpr hr)

中文:
定理 收敛.atTop_mul_const_of_neg'
  条件: (hr : r < 0) (hf : 收敛 f l atTop)
  证明: by
  simpa only [tendsto_neg_atTop_iff, mul_neg] using hf.atTop_mul_const' (neg_pos.mpr hr)

Depends on / 依赖: atTop_mul_const, hf.atTop_mul_const, mul_neg, neg_pos, neg_pos.mpr, tendsto_neg_atTop_iff
-/
theorem Tendsto.atTop_mul_const_of_neg' (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atBot := by
  simpa only [tendsto_neg_atTop_iff, mul_neg] using hf.atTop_mul_const' (neg_pos.mpr hr)

/--
theorem `Tendsto.atBot_mul_const'` / 定理 `Tendsto.atBot_mul_const'`

English:
theorem Tendsto.atBot_mul_const'
  given: (hr : 0 < r) (hf : Tendsto f l atBot)
  proof: by
  simp only [← tendsto_neg_atTop_iff, ← neg_mul] at hf ⊢
  exact hf.atTop_mul_const' hr

中文:
定理 收敛.atBot_mul_const'
  条件: (hr : 0 < r) (hf : 收敛 f l atBot)
  证明: by
  simp only [← tendsto_neg_atTop_iff, ← neg_mul] at hf ⊢
  exact hf.atTop_mul_const' hr

Depends on / 依赖: atTop_mul_const, hf.atTop_mul_const, neg_mul, tendsto_neg_atTop_iff
-/
theorem Tendsto.atBot_mul_const' (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atBot := by
  simp only [← tendsto_neg_atTop_iff, ← neg_mul] at hf ⊢
  exact hf.atTop_mul_const' hr

/--
theorem `Tendsto.atBot_mul_const_of_neg'` / 定理 `Tendsto.atBot_mul_const_of_neg'`

English:
theorem Tendsto.atBot_mul_const_of_neg'
  given: (hr : r < 0) (hf : Tendsto f l atBot)
  proof: by
  simpa only [mul_neg, tendsto_neg_atBot_iff] using hf.atBot_mul_const' (neg_pos.2 hr)

中文:
定理 收敛.atBot_mul_const_of_neg'
  条件: (hr : r < 0) (hf : 收敛 f l atBot)
  证明: by
  simpa only [mul_neg, tendsto_neg_atBot_iff] using hf.atBot_mul_const' (neg_pos.2 hr)

Depends on / 依赖: atBot_mul_const, hf.atBot_mul_const, mul_neg, neg_pos, tendsto_neg_atBot_iff
-/
theorem Tendsto.atBot_mul_const_of_neg' (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atTop := by
  simpa only [mul_neg, tendsto_neg_atBot_iff] using hf.atBot_mul_const' (neg_pos.2 hr)

end LinearOrderedRing

section LinearOrderedCancelAddCommMonoid

variable [AddCommMonoid R] [LinearOrder R] [IsOrderedCancelAddMonoid R] [Archimedean R]

/--
theorem `Tendsto.atTop_nsmul_const` / 定理 `Tendsto.atTop_nsmul_const`

English:
theorem Tendsto.atTop_nsmul_const
  given: {f : α -> Nat} (hr : 0 < r) (hf : Tendsto f l atTop)
  proof: by
  refine tendsto_atTop.mpr fun s => ?_
  obtain ⟨n : Nat, hn : s <= n • r⟩ := Archimedean.arch s hr
  exact (tendsto_atTop.mp hf n).mono fun a ha => hn.trans (nsmul_le_nsmul_left hr.le ha)

中文:
定理 收敛.atTop_nsmul_const
  条件: {f : α -> 自然数} (hr : 0 < r) (hf : 收敛 f l atTop)
  证明: by
  refine tendsto_atTop.mpr fun s => ?_
  obtain ⟨n : Nat, hn : s <= n • r⟩ := Archimedean.arch s hr
  exact (tendsto_atTop.mp hf n).mono fun a ha => hn.trans (nsmul_le_nsmul_left hr.le ha)

Depends on / 依赖: Archimedean, Archimedean.arch, hn.trans, hr.le, nsmul_le_nsmul_left, tendsto_atTop, tendsto_atTop.mp, tendsto_atTop.mpr
-/
theorem Tendsto.atTop_nsmul_const {f : α -> Nat} (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atTop := by
  refine tendsto_atTop.mpr fun s => ?_
  obtain ⟨n : Nat, hn : s <= n • r⟩ := Archimedean.arch s hr
  exact (tendsto_atTop.mp hf n).mono fun a ha => hn.trans (nsmul_le_nsmul_left hr.le ha)

end LinearOrderedCancelAddCommMonoid

section LinearOrderedAddCommGroup

variable [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] [Archimedean R]

/--
theorem `Tendsto.atTop_nsmul_neg_const` / 定理 `Tendsto.atTop_nsmul_neg_const`

English:
theorem Tendsto.atTop_nsmul_neg_const
  given: {f : α -> Nat} (hr : r < 0) (hf : Tendsto f l atTop)
  proof: by simpa using hf.atTop_nsmul_const (neg_pos.2 hr)

中文:
定理 收敛.atTop_nsmul_neg_const
  条件: {f : α -> 自然数} (hr : r < 0) (hf : 收敛 f l atTop)
  证明: by simpa using hf.atTop_nsmul_const (neg_pos.2 hr)

Depends on / 依赖: atTop_nsmul_const, hf.atTop_nsmul_const, neg_pos
-/
theorem Tendsto.atTop_nsmul_neg_const {f : α -> Nat} (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atBot := by simpa using hf.atTop_nsmul_const (neg_pos.2 hr)

/--
theorem `Tendsto.atTop_zsmul_const` / 定理 `Tendsto.atTop_zsmul_const`

English:
theorem Tendsto.atTop_zsmul_const
  given: {f : α -> Int} (hr : 0 < r) (hf : Tendsto f l atTop)
  proof: by
  refine tendsto_atTop.mpr fun s => ?_
  obtain ⟨n : Nat, hn : s <= n • r⟩ := Archimedean.arch s hr
  replace hn : s <= (n : Int) • r := by simpa
  exact (tendsto_atTop.mp hf n).mono fun a ha => hn.trans (zsmul_le_zsmul_left hr.le ha)

中文:
定理 收敛.atTop_zsmul_const
  条件: {f : α -> 整数} (hr : 0 < r) (hf : 收敛 f l atTop)
  证明: by
  refine tendsto_atTop.mpr fun s => ?_
  obtain ⟨n : Nat, hn : s <= n • r⟩ := Archimedean.arch s hr
  replace hn : s <= (n : Int) • r := by simpa
  exact (tendsto_atTop.mp hf n).mono fun a ha => hn.trans (zsmul_le_zsmul_left hr.le ha)

Depends on / 依赖: Archimedean, Archimedean.arch, hn.trans, hr.le, replace, tendsto_atTop, tendsto_atTop.mp, tendsto_atTop.mpr, zsmul_le_zsmul_left
-/
theorem Tendsto.atTop_zsmul_const {f : α -> Int} (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atTop := by
  refine tendsto_atTop.mpr fun s => ?_
  obtain ⟨n : Nat, hn : s <= n • r⟩ := Archimedean.arch s hr
  replace hn : s <= (n : Int) • r := by simpa
  exact (tendsto_atTop.mp hf n).mono fun a ha => hn.trans (zsmul_le_zsmul_left hr.le ha)

/--
theorem `Tendsto.atTop_zsmul_neg_const` / 定理 `Tendsto.atTop_zsmul_neg_const`

English:
theorem Tendsto.atTop_zsmul_neg_const
  given: {f : α -> Int} (hr : r < 0) (hf : Tendsto f l atTop)
  proof: by simpa using hf.atTop_zsmul_const (neg_pos.2 hr)

中文:
定理 收敛.atTop_zsmul_neg_const
  条件: {f : α -> 整数} (hr : r < 0) (hf : 收敛 f l atTop)
  证明: by simpa using hf.atTop_zsmul_const (neg_pos.2 hr)

Depends on / 依赖: atTop_zsmul_const, hf.atTop_zsmul_const, neg_pos
-/
theorem Tendsto.atTop_zsmul_neg_const {f : α -> Int} (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atBot := by simpa using hf.atTop_zsmul_const (neg_pos.2 hr)

/--
theorem `Tendsto.atBot_zsmul_const` / 定理 `Tendsto.atBot_zsmul_const`

English:
theorem Tendsto.atBot_zsmul_const
  given: {f : α -> Int} (hr : 0 < r) (hf : Tendsto f l atBot)
  proof: by
  simp only [← tendsto_neg_atTop_iff, ← neg_zsmul] at hf ⊢
  exact hf.atTop_zsmul_const hr

中文:
定理 收敛.atBot_zsmul_const
  条件: {f : α -> 整数} (hr : 0 < r) (hf : 收敛 f l atBot)
  证明: by
  simp only [← tendsto_neg_atTop_iff, ← neg_zsmul] at hf ⊢
  exact hf.atTop_zsmul_const hr

Depends on / 依赖: atTop_zsmul_const, hf.atTop_zsmul_const, neg_zsmul, tendsto_neg_atTop_iff
-/
theorem Tendsto.atBot_zsmul_const {f : α -> Int} (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x • r) l atBot := by
  simp only [← tendsto_neg_atTop_iff, ← neg_zsmul] at hf ⊢
  exact hf.atTop_zsmul_const hr

/--
theorem `Tendsto.atBot_zsmul_neg_const` / 定理 `Tendsto.atBot_zsmul_neg_const`

English:
theorem Tendsto.atBot_zsmul_neg_const
  given: {f : α -> Int} (hr : r < 0) (hf : Tendsto f l atBot)
  proof: by simpa using hf.atBot_zsmul_const (neg_pos.2 hr)

中文:
定理 收敛.atBot_zsmul_neg_const
  条件: {f : α -> 整数} (hr : r < 0) (hf : 收敛 f l atBot)
  证明: by simpa using hf.atBot_zsmul_const (neg_pos.2 hr)

Depends on / 依赖: atBot_zsmul_const, hf.atBot_zsmul_const, neg_pos
-/
theorem Tendsto.atBot_zsmul_neg_const {f : α -> Int} (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x • r) l atTop := by simpa using hf.atBot_zsmul_const (neg_pos.2 hr)

end LinearOrderedAddCommGroup

end Filter
