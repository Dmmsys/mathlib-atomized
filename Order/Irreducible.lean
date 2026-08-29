/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Irreducible and prime elements in an order

This file defines irreducible and prime elements in an order and shows that in a well-founded
lattice every element decomposes as a supremum of irreducible elements.

An element is sup-irreducible (resp. inf-irreducible) if it isn't `⊥` and can't be written as the
supremum of any strictly smaller elements. An element is sup-prime (resp. inf-prime) if it isn't `⊥`
and is greater than the supremum of any two elements less than it.

Primality implies irreducibility in general. The converse only holds in distributive lattices.
Both hold for all (non-minimal) elements in a linear order.

## Main declarations

* `SupIrred a`: Sup-irreducibility, `a` isn't minimal and `a = b ⊔ c → a = b ∨ a = c`
* `InfIrred a`: Inf-irreducibility, `a` isn't maximal and `a = b ⊓ c → a = b ∨ a = c`
* `SupPrime a`: Sup-primality, `a` isn't minimal and `a ≤ b ⊔ c → a ≤ b ∨ a ≤ c`
* `InfIrred a`: Inf-primality, `a` isn't maximal and `a ≥ b ⊓ c → a ≥ b ∨ a ≥ c`
* `exists_supIrred_decomposition`/`exists_infIrred_decomposition`: Decomposition into irreducibles
  in a well-founded semilattice.
-/

@[expose] public section


open Finset OrderDual

variable {ι α : Type*}

/-! ### Irreducible and prime elements -/


section SemilatticeSup

variable [SemilatticeSup α] {a b c : α}

/--
Definition of `SupIrred` / `SupIrred` 的定义

English:
definition SupIrred
  signature: (a : α)
  body: ¬IsMin a ∧ forall ⦃b c⦄, b ⊔ c = a -> b = a ∨ c = a

中文:
定义 SupIrred
  签名: (a : α)
  定义体: ¬IsMin a ∧ forall ⦃b c⦄, b ⊔ c = a -> b = a ∨ c = a
-/
def SupIrred (a : α) : Prop :=
  ¬IsMin a ∧ forall ⦃b c⦄, b ⊔ c = a -> b = a ∨ c = a

/--
Definition of `SupPrime` / `SupPrime` 的定义

English:
definition SupPrime
  signature: (a : α)
  body: ¬IsMin a ∧ forall ⦃b c⦄, a <= b ⊔ c -> a <= b ∨ a <= c

中文:
定义 SupPrime
  签名: (a : α)
  定义体: ¬IsMin a ∧ forall ⦃b c⦄, a <= b ⊔ c -> a <= b ∨ a <= c
-/
def SupPrime (a : α) : Prop :=
  ¬IsMin a ∧ forall ⦃b c⦄, a <= b ⊔ c -> a <= b ∨ a <= c

/--
theorem `SupIrred.not_isMin` / 定理 `SupIrred.not_isMin`

English:
theorem SupIrred.not_isMin
  given: (ha : SupIrred a)
  statement: ¬IsMin a
  proof: ha.1

中文:
定理 SupIrred.not_isMin
  条件: (ha : SupIrred a)
  结论: ¬IsMin a
  证明: ha.1
-/
theorem SupIrred.not_isMin (ha : SupIrred a) : ¬IsMin a :=
  ha.1

/--
theorem `SupPrime.not_isMin` / 定理 `SupPrime.not_isMin`

English:
theorem SupPrime.not_isMin
  given: (ha : SupPrime a)
  statement: ¬IsMin a
  proof: ha.1

中文:
定理 SupPrime.not_isMin
  条件: (ha : SupPrime a)
  结论: ¬IsMin a
  证明: ha.1
-/
theorem SupPrime.not_isMin (ha : SupPrime a) : ¬IsMin a :=
  ha.1

/--
theorem `IsMin.not_supIrred` / 定理 `IsMin.not_supIrred`

English:
theorem IsMin.not_supIrred
  given: (ha : IsMin a)
  statement: ¬SupIrred a
  proof: fun h => h.1 ha

中文:
定理 IsMin.not_supIrred
  条件: (ha : IsMin a)
  结论: ¬SupIrred a
  证明: fun h => h.1 ha

Depends on / 依赖: IsTwoSided, K.IsTwoSided
-/
theorem IsMin.not_supIrred (ha : IsMin a) : ¬SupIrred a := fun h => h.1 ha

/--
theorem `IsMin.not_supPrime` / 定理 `IsMin.not_supPrime`

English:
theorem IsMin.not_supPrime
  given: (ha : IsMin a)
  statement: ¬SupPrime a
  proof: fun h => h.1 ha

@[simp]

中文:
定理 IsMin.not_supPrime
  条件: (ha : IsMin a)
  结论: ¬SupPrime a
  证明: fun h => h.1 ha

@[simp]
-/
theorem IsMin.not_supPrime (ha : IsMin a) : ¬SupPrime a := fun h => h.1 ha

@[simp]
/--
theorem `not_supIrred` / 定理 `not_supIrred`

English:
theorem not_supIrred
  statement: ¬SupIrred a ↔ IsMin a ∨ exists b c, b ⊔ c = a ∧ b < a ∧ c < a
  proof: by
  rw [SupIrred]; rw [not_and_or]
  push Not
  rw [exists₂_congr]
  simp +contextual [@eq_comm _ _ a]

@[simp]

中文:
定理 not_supIrred
  结论: ¬SupIrred a ↔ IsMin a ∨ 存在 b c, b ⊔ c = a ∧ b < a ∧ c < a
  证明: by
  rw [SupIrred]; rw [not_and_or]
  push Not
  rw [exists₂_congr]
  simp +contextual [@eq_comm _ _ a]

@[simp]

Depends on / 依赖: SupIrred, contextual, eq_comm, not_and_or
-/
theorem not_supIrred : ¬SupIrred a ↔ IsMin a ∨ exists b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  rw [SupIrred]; rw [not_and_or]
  push Not
  rw [exists₂_congr]
  simp +contextual [@eq_comm _ _ a]

@[simp]
/--
theorem `not_supPrime` / 定理 `not_supPrime`

English:
theorem not_supPrime
  statement: ¬SupPrime a ↔ IsMin a ∨ exists b c, a <= b ⊔ c ∧ ¬a <= b ∧ ¬a <= c
  proof: by
  rw [SupPrime]; rw [not_and_or]; push Not; rfl

中文:
定理 not_supPrime
  结论: ¬SupPrime a ↔ IsMin a ∨ 存在 b c, a <= b ⊔ c ∧ ¬a <= b ∧ ¬a <= c
  证明: by
  rw [SupPrime]; rw [not_and_or]; push Not; rfl

Depends on / 依赖: SupPrime, not_and_or
-/
theorem not_supPrime : ¬SupPrime a ↔ IsMin a ∨ exists b c, a <= b ⊔ c ∧ ¬a <= b ∧ ¬a <= c := by
  rw [SupPrime]; rw [not_and_or]; push Not; rfl

/--
theorem `SupPrime.supIrred` / 定理 `SupPrime.supIrred`

English:
theorem SupPrime.supIrred
  statement: SupPrime a -> SupIrred a
  proof: And.imp_right fun h b c ha => by simpa [← ha] using h ha.ge

中文:
定理 SupPrime.supIrred
  结论: SupPrime a -> SupIrred a
  证明: And.imp_right fun h b c ha => by simpa [← ha] using h ha.ge
-/
protected theorem SupPrime.supIrred : SupPrime a -> SupIrred a :=
  And.imp_right fun h b c ha => by simpa [← ha] using h ha.ge

/--
theorem `SupPrime.le_sup` / 定理 `SupPrime.le_sup`

English:
theorem SupPrime.le_sup
  given: (ha : SupPrime a)
  statement: a <= b ⊔ c ↔ a <= b ∨ a <= c
  proof: ⟨fun h => ha.2 h, fun h => h.elim le_sup_of_le_left le_sup_of_le_right⟩

中文:
定理 SupPrime.le_sup
  条件: (ha : SupPrime a)
  结论: a <= b ⊔ c ↔ a <= b ∨ a <= c
  证明: ⟨fun h => ha.2 h, fun h => h.elim le_sup_of_le_left le_sup_of_le_right⟩

Depends on / 依赖: h.elim, le_sup_of_le_left, le_sup_of_le_right
-/
theorem SupPrime.le_sup (ha : SupPrime a) : a <= b ⊔ c ↔ a <= b ∨ a <= c :=
  ⟨fun h => ha.2 h, fun h => h.elim le_sup_of_le_left le_sup_of_le_right⟩

variable [OrderBot α] {s : Finset ι} {f : ι -> α}

@[simp]
/--
theorem `not_supIrred_bot` / 定理 `not_supIrred_bot`

English:
theorem not_supIrred_bot
  statement: ¬SupIrred (⊥ : α)
  proof: isMin_bot.not_supIrred

@[simp]

中文:
定理 not_supIrred_bot
  结论: ¬SupIrred (⊥ : α)
  证明: isMin_bot.not_supIrred

@[simp]

Depends on / 依赖: isMin_bot, isMin_bot.not_supIrred, not_supIrred
-/
theorem not_supIrred_bot : ¬SupIrred (⊥ : α) :=
  isMin_bot.not_supIrred

@[simp]
/--
theorem `not_supPrime_bot` / 定理 `not_supPrime_bot`

English:
theorem not_supPrime_bot
  statement: ¬SupPrime (⊥ : α)
  proof: isMin_bot.not_supPrime

中文:
定理 not_supPrime_bot
  结论: ¬SupPrime (⊥ : α)
  证明: isMin_bot.not_supPrime

Depends on / 依赖: isMin_bot, isMin_bot.not_supPrime, not_supPrime
-/
theorem not_supPrime_bot : ¬SupPrime (⊥ : α) :=
  isMin_bot.not_supPrime

/--
theorem `SupIrred.ne_bot` / 定理 `SupIrred.ne_bot`

English:
theorem SupIrred.ne_bot
  given: (ha : SupIrred a)
  statement: a != ⊥
  proof: by rintro rfl; exact not_supIrred_bot ha

中文:
定理 SupIrred.ne_bot
  条件: (ha : SupIrred a)
  结论: a != ⊥
  证明: by rintro rfl; exact not_supIrred_bot ha

Depends on / 依赖: not_supIrred_bot
-/
theorem SupIrred.ne_bot (ha : SupIrred a) : a != ⊥ := by rintro rfl; exact not_supIrred_bot ha

/--
theorem `SupPrime.ne_bot` / 定理 `SupPrime.ne_bot`

English:
theorem SupPrime.ne_bot
  given: (ha : SupPrime a)
  statement: a != ⊥
  proof: by rintro rfl; exact not_supPrime_bot ha

中文:
定理 SupPrime.ne_bot
  条件: (ha : SupPrime a)
  结论: a != ⊥
  证明: by rintro rfl; exact not_supPrime_bot ha

Depends on / 依赖: not_supPrime_bot
-/
theorem SupPrime.ne_bot (ha : SupPrime a) : a != ⊥ := by rintro rfl; exact not_supPrime_bot ha

/--
theorem `SupIrred.finset_sup_eq` / 定理 `SupIrred.finset_sup_eq`

English:
theorem SupIrred.finset_sup_eq
  given: (ha : SupIrred a) (h : s.sup f = a)
  statement: exists i in s, f i = a
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simpa [ha.ne_bot] using h.symm
  | insert i s _ ih =>
    simp only [exists_mem_insert] at ih ⊢
    rw [sup_insert] at h
    exact (ha.2 h).imp_right ih

中文:
定理 SupIrred.finset_sup_eq
  条件: (ha : SupIrred a) (h : s.sup f = a)
  结论: 存在 i in s, f i = a
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simpa [ha.ne_bot] using h.symm
  | insert i s _ ih =>
    simp only [exists_mem_insert] at ih ⊢
    rw [sup_insert] at h
    exact (ha.2 h).imp_right ih

Depends on / 依赖: Finset, Finset.induction, classical, exists_mem_insert, h.symm, ha.ne_bot, imp_right, insert, ne_bot, sup_insert
-/
theorem SupIrred.finset_sup_eq (ha : SupIrred a) (h : s.sup f = a) : exists i in s, f i = a := by
  classical
  induction s using Finset.induction with
  | empty => simpa [ha.ne_bot] using h.symm
  | insert i s _ ih =>
    simp only [exists_mem_insert] at ih ⊢
    rw [sup_insert] at h
    exact (ha.2 h).imp_right ih

/--
theorem `SupPrime.le_finset_sup` / 定理 `SupPrime.le_finset_sup`

English:
theorem SupPrime.le_finset_sup
  given: (ha : SupPrime a)
  statement: a <= s.sup f ↔ exists i in s, a <= f i
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp [ha.ne_bot]
  | insert i s _ ih => simp only [exists_mem_insert, sup_insert, ha.le_sup, ih]

中文:
定理 SupPrime.le_finset_sup
  条件: (ha : SupPrime a)
  结论: a <= s.sup f ↔ 存在 i in s, a <= f i
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp [ha.ne_bot]
  | insert i s _ ih => simp only [exists_mem_insert, sup_insert, ha.le_sup, ih]

Depends on / 依赖: Finset, Finset.induction, classical, exists_mem_insert, ha.le_sup, ha.ne_bot, insert, le_sup, ne_bot, sup_insert
-/
theorem SupPrime.le_finset_sup (ha : SupPrime a) : a <= s.sup f ↔ exists i in s, a <= f i := by
  classical
  induction s using Finset.induction with
  | empty => simp [ha.ne_bot]
  | insert i s _ ih => simp only [exists_mem_insert, sup_insert, ha.le_sup, ih]

variable [WellFoundedLT α]

/--
theorem `exists_supIrred_decomposition` / 定理 `exists_supIrred_decomposition`

English:
theorem exists_supIrred_decomposition
  given: (a : α)
  proof: by
  classical
  apply WellFoundedLT.induction a _
  clear a
  rintro a ih
  by_cases ha : SupIrred a
  · exact ⟨{a}, by simp [ha]⟩
  rw [not_supIrred] at ha
  obtain ha | ⟨b, c, rfl, hb, hc⟩ := ha
  · exact ⟨∅, by simp [ha.eq_bot]⟩
  obtain ⟨s, rfl, hs⟩ := ih _ hb
  obtain ⟨t, rfl, ht⟩ := ih _ hc
 

中文:
定理 exists_supIrred_decomposition
  条件: (a : α)
  证明: by
  classical
  apply WellFoundedLT.induction a _
  clear a
  rintro a ih
  by_cases ha : SupIrred a
  · exact ⟨{a}, by simp [ha]⟩
  rw [not_supIrred] at ha
  obtain ha | ⟨b, c, rfl, hb, hc⟩ := ha
  · exact ⟨∅, by simp [ha.eq_bot]⟩
  obtain ⟨s, rfl, hs⟩ := ih _ hb
  obtain ⟨t, rfl, ht⟩ := ih _ hc
 

Depends on / 依赖: SupIrred, WellFoundedLT, WellFoundedLT.induction, classical, eq_bot, forall_mem_union, ha.eq_bot, not_supIrred, sup_union
-/
theorem exists_supIrred_decomposition (a : α) :
    exists s : Finset α, s.sup id = a ∧ forall ⦃b⦄, b in s -> SupIrred b := by
  classical
  apply WellFoundedLT.induction a _
  clear a
  rintro a ih
  by_cases ha : SupIrred a
  · exact ⟨{a}, by simp [ha]⟩
  rw [not_supIrred] at ha
  obtain ha | ⟨b, c, rfl, hb, hc⟩ := ha
  · exact ⟨∅, by simp [ha.eq_bot]⟩
  obtain ⟨s, rfl, hs⟩ := ih _ hb
  obtain ⟨t, rfl, ht⟩ := ih _ hc
  exact ⟨s union t, sup_union, forall_mem_union.2 ⟨hs, ht⟩⟩

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α] {a b c : α}

/--
Definition of `InfIrred` / `InfIrred` 的定义

English:
definition InfIrred
  signature: (a : α)
  body: ¬IsMax a ∧ forall ⦃b c⦄, b ⊓ c = a -> b = a ∨ c = a

中文:
定义 InfIrred
  签名: (a : α)
  定义体: ¬IsMax a ∧ forall ⦃b c⦄, b ⊓ c = a -> b = a ∨ c = a
-/
def InfIrred (a : α) : Prop :=
  ¬IsMax a ∧ forall ⦃b c⦄, b ⊓ c = a -> b = a ∨ c = a

/--
Definition of `InfPrime` / `InfPrime` 的定义

English:
definition InfPrime
  signature: (a : α)
  body: ¬IsMax a ∧ forall ⦃b c⦄, b ⊓ c <= a -> b <= a ∨ c <= a

@[simp]

中文:
定义 InfPrime
  签名: (a : α)
  定义体: ¬IsMax a ∧ forall ⦃b c⦄, b ⊓ c <= a -> b <= a ∨ c <= a

@[simp]
-/
def InfPrime (a : α) : Prop :=
  ¬IsMax a ∧ forall ⦃b c⦄, b ⊓ c <= a -> b <= a ∨ c <= a

@[simp]
/--
theorem `IsMax.not_infIrred` / 定理 `IsMax.not_infIrred`

English:
theorem IsMax.not_infIrred
  given: (ha : IsMax a)
  statement: ¬InfIrred a
  proof: fun h => h.1 ha

@[simp]

中文:
定理 IsMax.not_infIrred
  条件: (ha : IsMax a)
  结论: ¬InfIrred a
  证明: fun h => h.1 ha

@[simp]
-/
theorem IsMax.not_infIrred (ha : IsMax a) : ¬InfIrred a := fun h => h.1 ha

@[simp]
/--
theorem `IsMax.not_infPrime` / 定理 `IsMax.not_infPrime`

English:
theorem IsMax.not_infPrime
  given: (ha : IsMax a)
  statement: ¬InfPrime a
  proof: fun h => h.1 ha

@[simp]

中文:
定理 IsMax.not_infPrime
  条件: (ha : IsMax a)
  结论: ¬InfPrime a
  证明: fun h => h.1 ha

@[simp]
-/
theorem IsMax.not_infPrime (ha : IsMax a) : ¬InfPrime a := fun h => h.1 ha

@[simp]
/--
theorem `not_infIrred` / 定理 `not_infIrred`

English:
theorem not_infIrred
  statement: ¬InfIrred a ↔ IsMax a ∨ exists b c, b ⊓ c = a ∧ a < b ∧ a < c
  proof: @not_supIrred αᵒᵈ _ _

@[simp]

中文:
定理 not_infIrred
  结论: ¬InfIrred a ↔ IsMax a ∨ 存在 b c, b ⊓ c = a ∧ a < b ∧ a < c
  证明: @not_supIrred αᵒᵈ _ _

@[simp]

Depends on / 依赖: not_supIrred
-/
theorem not_infIrred : ¬InfIrred a ↔ IsMax a ∨ exists b c, b ⊓ c = a ∧ a < b ∧ a < c :=
  @not_supIrred αᵒᵈ _ _

@[simp]
/--
theorem `not_infPrime` / 定理 `not_infPrime`

English:
theorem not_infPrime
  statement: ¬InfPrime a ↔ IsMax a ∨ exists b c, b ⊓ c <= a ∧ ¬b <= a ∧ ¬c <= a
  proof: @not_supPrime αᵒᵈ _ _

中文:
定理 not_infPrime
  结论: ¬InfPrime a ↔ IsMax a ∨ 存在 b c, b ⊓ c <= a ∧ ¬b <= a ∧ ¬c <= a
  证明: @not_supPrime αᵒᵈ _ _

Depends on / 依赖: not_supPrime
-/
theorem not_infPrime : ¬InfPrime a ↔ IsMax a ∨ exists b c, b ⊓ c <= a ∧ ¬b <= a ∧ ¬c <= a :=
  @not_supPrime αᵒᵈ _ _

/--
theorem `InfPrime.infIrred` / 定理 `InfPrime.infIrred`

English:
theorem InfPrime.infIrred
  statement: InfPrime a -> InfIrred a
  proof: And.imp_right fun h b c ha => by simpa [← ha] using h ha.le

中文:
定理 InfPrime.infIrred
  结论: InfPrime a -> InfIrred a
  证明: And.imp_right fun h b c ha => by simpa [← ha] using h ha.le
-/
protected theorem InfPrime.infIrred : InfPrime a -> InfIrred a :=
  And.imp_right fun h b c ha => by simpa [← ha] using h ha.le

/--
theorem `InfPrime.inf_le` / 定理 `InfPrime.inf_le`

English:
theorem InfPrime.inf_le
  given: (ha : InfPrime a)
  statement: b ⊓ c <= a ↔ b <= a ∨ c <= a
  proof: ⟨fun h => ha.2 h, fun h => h.elim inf_le_of_left_le inf_le_of_right_le⟩

中文:
定理 InfPrime.inf_le
  条件: (ha : InfPrime a)
  结论: b ⊓ c <= a ↔ b <= a ∨ c <= a
  证明: ⟨fun h => ha.2 h, fun h => h.elim inf_le_of_left_le inf_le_of_right_le⟩

Depends on / 依赖: h.elim, inf_le_of_left_le, inf_le_of_right_le
-/
theorem InfPrime.inf_le (ha : InfPrime a) : b ⊓ c <= a ↔ b <= a ∨ c <= a :=
  ⟨fun h => ha.2 h, fun h => h.elim inf_le_of_left_le inf_le_of_right_le⟩

variable [OrderTop α] {s : Finset ι} {f : ι -> α}

/--
theorem `not_infIrred_top` / 定理 `not_infIrred_top`

English:
theorem not_infIrred_top
  statement: ¬InfIrred (⊤ : α)
  proof: isMax_top.not_infIrred

中文:
定理 not_infIrred_top
  结论: ¬InfIrred (⊤ : α)
  证明: isMax_top.not_infIrred

Depends on / 依赖: isMax_top, isMax_top.not_infIrred, not_infIrred
-/
theorem not_infIrred_top : ¬InfIrred (⊤ : α) :=
  isMax_top.not_infIrred

/--
theorem `not_infPrime_top` / 定理 `not_infPrime_top`

English:
theorem not_infPrime_top
  statement: ¬InfPrime (⊤ : α)
  proof: isMax_top.not_infPrime

中文:
定理 not_infPrime_top
  结论: ¬InfPrime (⊤ : α)
  证明: isMax_top.not_infPrime

Depends on / 依赖: isMax_top, isMax_top.not_infPrime, not_infPrime
-/
theorem not_infPrime_top : ¬InfPrime (⊤ : α) :=
  isMax_top.not_infPrime

/--
theorem `InfIrred.ne_top` / 定理 `InfIrred.ne_top`

English:
theorem InfIrred.ne_top
  given: (ha : InfIrred a)
  statement: a != ⊤
  proof: by rintro rfl; exact not_infIrred_top ha

中文:
定理 InfIrred.ne_top
  条件: (ha : InfIrred a)
  结论: a != ⊤
  证明: by rintro rfl; exact not_infIrred_top ha

Depends on / 依赖: not_infIrred_top
-/
theorem InfIrred.ne_top (ha : InfIrred a) : a != ⊤ := by rintro rfl; exact not_infIrred_top ha

/--
theorem `InfPrime.ne_top` / 定理 `InfPrime.ne_top`

English:
theorem InfPrime.ne_top
  given: (ha : InfPrime a)
  statement: a != ⊤
  proof: by rintro rfl; exact not_infPrime_top ha

中文:
定理 InfPrime.ne_top
  条件: (ha : InfPrime a)
  结论: a != ⊤
  证明: by rintro rfl; exact not_infPrime_top ha

Depends on / 依赖: not_infPrime_top
-/
theorem InfPrime.ne_top (ha : InfPrime a) : a != ⊤ := by rintro rfl; exact not_infPrime_top ha

/--
theorem `InfIrred.finset_inf_eq` / 定理 `InfIrred.finset_inf_eq`

English:
theorem InfIrred.finset_inf_eq
  statement: InfIrred a -> s.inf f = a -> exists i in s, f i = a
  proof: @SupIrred.finset_sup_eq _ αᵒᵈ _ _ _ _ _

中文:
定理 InfIrred.finset_inf_eq
  结论: InfIrred a -> s.inf f = a -> 存在 i in s, f i = a
  证明: @SupIrred.finset_sup_eq _ αᵒᵈ _ _ _ _ _

Depends on / 依赖: SupIrred, SupIrred.finset_sup_eq, finset_sup_eq
-/
theorem InfIrred.finset_inf_eq : InfIrred a -> s.inf f = a -> exists i in s, f i = a :=
  @SupIrred.finset_sup_eq _ αᵒᵈ _ _ _ _ _

/--
theorem `InfPrime.finset_inf_le` / 定理 `InfPrime.finset_inf_le`

English:
theorem InfPrime.finset_inf_le
  given: (ha : InfPrime a)
  statement: s.inf f <= a ↔ exists i in s, f i <= a
  proof: @SupPrime.le_finset_sup _ αᵒᵈ _ _ _ _ _ ha

中文:
定理 InfPrime.finset_inf_le
  条件: (ha : InfPrime a)
  结论: s.inf f <= a ↔ 存在 i in s, f i <= a
  证明: @SupPrime.le_finset_sup _ αᵒᵈ _ _ _ _ _ ha

Depends on / 依赖: SupPrime, SupPrime.le_finset_sup, le_finset_sup
-/
theorem InfPrime.finset_inf_le (ha : InfPrime a) : s.inf f <= a ↔ exists i in s, f i <= a :=
  @SupPrime.le_finset_sup _ αᵒᵈ _ _ _ _ _ ha

variable [WellFoundedGT α]

/--
theorem `exists_infIrred_decomposition` / 定理 `exists_infIrred_decomposition`

English:
theorem exists_infIrred_decomposition
  given: (a : α)
  proof: exists_supIrred_decomposition (α := αᵒᵈ) _

中文:
定理 exists_infIrred_decomposition
  条件: (a : α)
  证明: exists_supIrred_decomposition (α := αᵒᵈ) _

Depends on / 依赖: exists_supIrred_decomposition
-/
theorem exists_infIrred_decomposition (a : α) :
    exists s : Finset α, s.inf id = a ∧ forall ⦃b⦄, b in s -> InfIrred b :=
  exists_supIrred_decomposition (α := αᵒᵈ) _

end SemilatticeInf

section SemilatticeSup

variable [SemilatticeSup α]

@[simp]
/--
theorem `infIrred_toDual` / 定理 `infIrred_toDual`

English:
theorem infIrred_toDual
  given: {a : α}
  statement: InfIrred (toDual a) ↔ SupIrred a
  proof: Iff.rfl

@[simp]

中文:
定理 infIrred_toDual
  条件: {a : α}
  结论: InfIrred (toDual a) ↔ SupIrred a
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem infIrred_toDual {a : α} : InfIrred (toDual a) ↔ SupIrred a :=
  Iff.rfl

@[simp]
/--
theorem `infPrime_toDual` / 定理 `infPrime_toDual`

English:
theorem infPrime_toDual
  given: {a : α}
  statement: InfPrime (toDual a) ↔ SupPrime a
  proof: Iff.rfl

@[simp]

中文:
定理 infPrime_toDual
  条件: {a : α}
  结论: InfPrime (toDual a) ↔ SupPrime a
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem infPrime_toDual {a : α} : InfPrime (toDual a) ↔ SupPrime a :=
  Iff.rfl

@[simp]
/--
theorem `supIrred_ofDual` / 定理 `supIrred_ofDual`

English:
theorem supIrred_ofDual
  given: {a : αᵒᵈ}
  statement: SupIrred (ofDual a) ↔ InfIrred a
  proof: Iff.rfl

@[simp]

中文:
定理 supIrred_ofDual
  条件: {a : αᵒᵈ}
  结论: SupIrred (ofDual a) ↔ InfIrred a
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem supIrred_ofDual {a : αᵒᵈ} : SupIrred (ofDual a) ↔ InfIrred a :=
  Iff.rfl

@[simp]
/--
theorem `supPrime_ofDual` / 定理 `supPrime_ofDual`

English:
theorem supPrime_ofDual
  given: {a : αᵒᵈ}
  statement: SupPrime (ofDual a) ↔ InfPrime a
  proof: Iff.rfl

alias ⟨_, SupIrred.dual⟩ := infIrred_toDual

alias ⟨_, SupPrime.dual⟩ := infPrime_toDual

alias ⟨_, InfIrred.ofDual⟩ := supIrred_ofDual

alias ⟨_, InfPrime.ofDual⟩ := supPrime_ofDual

中文:
定理 supPrime_ofDual
  条件: {a : αᵒᵈ}
  结论: SupPrime (ofDual a) ↔ InfPrime a
  证明: Iff.rfl

alias ⟨_, SupIrred.dual⟩ := infIrred_toDual

alias ⟨_, SupPrime.dual⟩ := infPrime_toDual

alias ⟨_, InfIrred.ofDual⟩ := supIrred_ofDual

alias ⟨_, InfPrime.ofDual⟩ := supPrime_ofDual

Depends on / 依赖: Iff.rfl
-/
theorem supPrime_ofDual {a : αᵒᵈ} : SupPrime (ofDual a) ↔ InfPrime a :=
  Iff.rfl

alias ⟨_, SupIrred.dual⟩ := infIrred_toDual

alias ⟨_, SupPrime.dual⟩ := infPrime_toDual

alias ⟨_, InfIrred.ofDual⟩ := supIrred_ofDual

alias ⟨_, InfPrime.ofDual⟩ := supPrime_ofDual

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α]

@[simp]
/--
theorem `supIrred_toDual` / 定理 `supIrred_toDual`

English:
theorem supIrred_toDual
  given: {a : α}
  statement: SupIrred (toDual a) ↔ InfIrred a
  proof: Iff.rfl

@[simp]

中文:
定理 supIrred_toDual
  条件: {a : α}
  结论: SupIrred (toDual a) ↔ InfIrred a
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem supIrred_toDual {a : α} : SupIrred (toDual a) ↔ InfIrred a :=
  Iff.rfl

@[simp]
/--
theorem `supPrime_toDual` / 定理 `supPrime_toDual`

English:
theorem supPrime_toDual
  given: {a : α}
  statement: SupPrime (toDual a) ↔ InfPrime a
  proof: Iff.rfl

@[simp]

中文:
定理 supPrime_toDual
  条件: {a : α}
  结论: SupPrime (toDual a) ↔ InfPrime a
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem supPrime_toDual {a : α} : SupPrime (toDual a) ↔ InfPrime a :=
  Iff.rfl

@[simp]
/--
theorem `infIrred_ofDual` / 定理 `infIrred_ofDual`

English:
theorem infIrred_ofDual
  given: {a : αᵒᵈ}
  statement: InfIrred (ofDual a) ↔ SupIrred a
  proof: Iff.rfl

@[simp]

中文:
定理 infIrred_ofDual
  条件: {a : αᵒᵈ}
  结论: InfIrred (ofDual a) ↔ SupIrred a
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem infIrred_ofDual {a : αᵒᵈ} : InfIrred (ofDual a) ↔ SupIrred a :=
  Iff.rfl

@[simp]
/--
theorem `infPrime_ofDual` / 定理 `infPrime_ofDual`

English:
theorem infPrime_ofDual
  given: {a : αᵒᵈ}
  statement: InfPrime (ofDual a) ↔ SupPrime a
  proof: Iff.rfl

alias ⟨_, InfIrred.dual⟩ := supIrred_toDual

alias ⟨_, InfPrime.dual⟩ := supPrime_toDual

alias ⟨_, SupIrred.ofDual⟩ := infIrred_ofDual

alias ⟨_, SupPrime.ofDual⟩ := infPrime_ofDual

中文:
定理 infPrime_ofDual
  条件: {a : αᵒᵈ}
  结论: InfPrime (ofDual a) ↔ SupPrime a
  证明: Iff.rfl

alias ⟨_, InfIrred.dual⟩ := supIrred_toDual

alias ⟨_, InfPrime.dual⟩ := supPrime_toDual

alias ⟨_, SupIrred.ofDual⟩ := infIrred_ofDual

alias ⟨_, SupPrime.ofDual⟩ := infPrime_ofDual

Depends on / 依赖: Iff.rfl
-/
theorem infPrime_ofDual {a : αᵒᵈ} : InfPrime (ofDual a) ↔ SupPrime a :=
  Iff.rfl

alias ⟨_, InfIrred.dual⟩ := supIrred_toDual

alias ⟨_, InfPrime.dual⟩ := supPrime_toDual

alias ⟨_, SupIrred.ofDual⟩ := infIrred_ofDual

alias ⟨_, SupPrime.ofDual⟩ := infPrime_ofDual

end SemilatticeInf

section DistribLattice

variable [DistribLattice α] {a : α}

@[simp]
/--
theorem `supPrime_iff_supIrred` / 定理 `supPrime_iff_supIrred`

English:
theorem supPrime_iff_supIrred
  statement: SupPrime a ↔ SupIrred a
  proof: ⟨SupPrime.supIrred,
    And.imp_right fun h b c => by simp_rw [← inf_eq_left, inf_sup_left]; exact @h _ _⟩

@[simp]

中文:
定理 supPrime_iff_supIrred
  结论: SupPrime a ↔ SupIrred a
  证明: ⟨SupPrime.supIrred,
    And.imp_right fun h b c => by simp_rw [← inf_eq_left, inf_sup_left]; exact @h _ _⟩

@[simp]

Depends on / 依赖: And.imp_right, SupPrime, SupPrime.supIrred, imp_right, inf_eq_left, inf_sup_left, simp_rw, supIrred
-/
theorem supPrime_iff_supIrred : SupPrime a ↔ SupIrred a :=
  ⟨SupPrime.supIrred,
    And.imp_right fun h b c => by simp_rw [← inf_eq_left, inf_sup_left]; exact @h _ _⟩

@[simp]
/--
theorem `infPrime_iff_infIrred` / 定理 `infPrime_iff_infIrred`

English:
theorem infPrime_iff_infIrred
  statement: InfPrime a ↔ InfIrred a
  proof: ⟨InfPrime.infIrred,
    And.imp_right fun h b c => by simp_rw [← sup_eq_left, sup_inf_left]; exact @h _ _⟩

protected alias ⟨_, SupIrred.supPrime⟩ := supPrime_iff_supIrred
protected alias ⟨_, InfIrred.infPrime⟩ := infPrime_iff_infIrred

中文:
定理 infPrime_iff_infIrred
  结论: InfPrime a ↔ InfIrred a
  证明: ⟨InfPrime.infIrred,
    And.imp_right fun h b c => by simp_rw [← sup_eq_left, sup_inf_left]; exact @h _ _⟩

protected alias ⟨_, SupIrred.supPrime⟩ := supPrime_iff_supIrred
protected alias ⟨_, InfIrred.infPrime⟩ := infPrime_iff_infIrred

Depends on / 依赖: And.imp_right, InfPrime, InfPrime.infIrred, imp_right, infIrred, simp_rw, sup_eq_left, sup_inf_left
-/
theorem infPrime_iff_infIrred : InfPrime a ↔ InfIrred a :=
  ⟨InfPrime.infIrred,
    And.imp_right fun h b c => by simp_rw [← sup_eq_left, sup_inf_left]; exact @h _ _⟩

protected alias ⟨_, SupIrred.supPrime⟩ := supPrime_iff_supIrred
protected alias ⟨_, InfIrred.infPrime⟩ := infPrime_iff_infIrred

end DistribLattice

section LinearOrder

variable [LinearOrder α] {a : α}

/--
theorem `supPrime_iff_not_isMin` / 定理 `supPrime_iff_not_isMin`

English:
theorem supPrime_iff_not_isMin
  statement: SupPrime a ↔ ¬IsMin a
  proof: and_iff_left by simp

中文:
定理 supPrime_iff_not_isMin
  结论: SupPrime a ↔ ¬IsMin a
  证明: and_iff_left by simp

Depends on / 依赖: and_iff_left
-/
theorem supPrime_iff_not_isMin : SupPrime a ↔ ¬IsMin a :=
and_iff_left by simp

/--
theorem `infPrime_iff_not_isMax` / 定理 `infPrime_iff_not_isMax`

English:
theorem infPrime_iff_not_isMax
  statement: InfPrime a ↔ ¬IsMax a
  proof: and_iff_left by simp

@[simp]

中文:
定理 infPrime_iff_not_isMax
  结论: InfPrime a ↔ ¬IsMax a
  证明: and_iff_left by simp

@[simp]

Depends on / 依赖: and_iff_left
-/
theorem infPrime_iff_not_isMax : InfPrime a ↔ ¬IsMax a :=
and_iff_left by simp

@[simp]
/--
theorem `supIrred_iff_not_isMin` / 定理 `supIrred_iff_not_isMin`

English:
theorem supIrred_iff_not_isMin
  statement: SupIrred a ↔ ¬IsMin a
  proof: and_iff_left fun _ _ => by simpa only [max_eq_iff] using Or.imp And.left And.left

@[simp]

中文:
定理 supIrred_iff_not_isMin
  结论: SupIrred a ↔ ¬IsMin a
  证明: and_iff_left fun _ _ => by simpa only [max_eq_iff] using Or.imp And.left And.left

@[simp]

Depends on / 依赖: And.left, Or.imp, and_iff_left, max_eq_iff
-/
theorem supIrred_iff_not_isMin : SupIrred a ↔ ¬IsMin a :=
  and_iff_left fun _ _ => by simpa only [max_eq_iff] using Or.imp And.left And.left

@[simp]
/--
theorem `infIrred_iff_not_isMax` / 定理 `infIrred_iff_not_isMax`

English:
theorem infIrred_iff_not_isMax
  statement: InfIrred a ↔ ¬IsMax a
  proof: and_iff_left fun _ _ => by simpa only [min_eq_iff] using Or.imp And.left And.left

中文:
定理 infIrred_iff_not_isMax
  结论: InfIrred a ↔ ¬IsMax a
  证明: and_iff_left fun _ _ => by simpa only [min_eq_iff] using Or.imp And.left And.left

Depends on / 依赖: And.left, Or.imp, and_iff_left, min_eq_iff
-/
theorem infIrred_iff_not_isMax : InfIrred a ↔ ¬IsMax a :=
  and_iff_left fun _ _ => by simpa only [min_eq_iff] using Or.imp And.left And.left

end LinearOrder
