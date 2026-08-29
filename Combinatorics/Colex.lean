/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Finset.Slice
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Order.SupClosed
public import Mathlib.Order.UpperLower.Closure

/-!
# Colexicographic order

We define the colex order for finite sets, and give a couple of important lemmas and properties
relating to it.

The colex ordering likes to avoid large values: If the biggest element of `t` is bigger than all
elements of `s`, then `s < t`.

In the special case of `ℕ`, it can be thought of as the "binary" ordering. That is, order `s` based
on $∑_{i ∈ s} 2^i$. It's defined here on `Finset α` for any linear order `α`.

In the context of the Kruskal-Katona theorem, we are interested in how colex behaves for sets of a
fixed size. For example, for size 3, the colex order on ℕ starts
`012, 013, 023, 123, 014, 024, 124, 034, 134, 234, ...`

## Main statements

* Colex order properties - linearity, decidability and so on.
* `Finset.Colex.forall_lt_mono`: if `s < t` in colex, and everything in `t` is `< a`, then
  everything in `s` is `< a`. This confirms the idea that an enumeration under colex will exhaust
  all sets using elements `< a` before allowing `a` to be included.
* `Finset.toColex_image_le_toColex_image`: Strictly monotone functions preserve colex.
* `Finset.geomSum_le_geomSum_iff_toColex_le_toColex`: Colex for α = ℕ is the same as binary.
  This also proves binary expansions are unique.

## See also

Related files are:
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σ' i, α i`.
* `Data.Sigma.Order`: Lexicographic order on `Σ i, α i`.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.

## TODO

* Generalise `Colex.initSeg` so that it applies to `ℕ`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

colex, colexicographic, binary
-/

@[expose] public section

open Function

variable {α β : Type*}

namespace Finset

open Colex

namespace Colex
section PartialOrder
variable [PartialOrder α] [PartialOrder β] {f : α -> β} {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)}
  {s t u : Finset α} {a b : α}

/--
Instance `instLE` / 实例 `instLE`

English:
instance instLE
  signature: : LE (Colex (Finset α)) where
  body: forall ⦃a⦄, a in ofColex s -> a ∉ ofColex t -> exists b, b in ofColex t ∧ b ∉ ofColex s ∧ a <= b

中文:
实例 instLE
  签名: : LE (Colex (有限集 α)) where
  定义体: forall ⦃a⦄, a in ofColex s -> a ∉ ofColex t -> exists b, b in ofColex t ∧ b ∉ ofColex s ∧ a <= b

Depends on / 依赖: ofColex
-/
instance instLE : LE (Colex (Finset α)) where
  le s t := forall ⦃a⦄, a in ofColex s -> a ∉ ofColex t -> exists b, b in ofColex t ∧ b ∉ ofColex s ∧ a <= b

-- TODO: This lemma is weirdly useful given how strange its statement is.
-- Is there a nicer statement? Should this lemma be made public?
/--
lemma `trans_aux` / 引理 `trans_aux`

English:
lemma trans_aux
  statement: (hst : toColex s <= toColex t) (htu : toColex t <= toColex u)
  proof: by
  classical
  let s' : Finset α := {b in s | b ∉ t ∧ a <= b}
  have ⟨b, hb, hbmax⟩ := s'.exists_maximal ⟨a, by simp [s', has, hat]⟩
  simp only [s', mem_filter, and_imp] at hb hbmax
  have ⟨c, hct, hcs, hbc⟩ := hst hb.1 hb.2.1
  by_cases hcu : c in u
  · exact ⟨c, hcu, hcs, hb.2.2.trans hbc⟩
  ha

中文:
引理 trans_aux
  结论: (hst : toColex s <= toColex t) (htu : toColex t <= toColex u)
  证明: by
  classical
  let s' : Finset α := {b in s | b ∉ t ∧ a <= b}
  have ⟨b, hb, hbmax⟩ := s'.exists_maximal ⟨a, by simp [s', has, hat]⟩
  simp only [s', mem_filter, and_imp] at hb hbmax
  have ⟨c, hct, hcs, hbc⟩ := hst hb.1 hb.2.1
  by_cases hcu : c in u
  · exact ⟨c, hcu, hcs, hb.2.2.trans hbc⟩
  ha
-/
private lemma trans_aux (hst : toColex s <= toColex t) (htu : toColex t <= toColex u)
    (has : a in s) (hat : a ∉ t) : exists b, b in u ∧ b ∉ s ∧ a <= b := by
  classical
  let s' : Finset α := {b in s | b ∉ t ∧ a <= b}
  have ⟨b, hb, hbmax⟩ := s'.exists_maximal ⟨a, by simp [s', has, hat]⟩
  simp only [s', mem_filter, and_imp] at hb hbmax
  have ⟨c, hct, hcs, hbc⟩ := hst hb.1 hb.2.1
  by_cases hcu : c in u
  · exact ⟨c, hcu, hcs, hb.2.2.trans hbc⟩
  have ⟨d, hdu, hdt, hcd⟩ := htu hct hcu
have had : a <= d := hb.2.2.trans hbc.trans hcd
  refine ⟨d, hdu, fun hds => not_lt_iff_le_imp_ge.2 (hbmax hds hdt had) ?_, had⟩
exact hbc.trans_lt hcd.lt_of_ne ne_of_mem_of_not_mem hct hdt

set_option backward.privateInPublic true in
/--
lemma `antisymm_aux` / 引理 `antisymm_aux`

English:
lemma antisymm_aux
  given: (hst : toColex s <= toColex t) (hts : toColex t <= toColex s)
  statement: s subseteq t
  proof: by
  intro a has
  by_contra hat
  have ⟨_b, hb₁, hb₂, _⟩ := trans_aux hst hts has hat
  exact hb₂ hb₁

中文:
引理 antisymm_aux
  条件: (hst : toColex s <= toColex t) (hts : toColex t <= toColex s)
  结论: s subseteq t
  证明: by
  intro a has
  by_contra hat
  have ⟨_b, hb₁, hb₂, _⟩ := trans_aux hst hts has hat
  exact hb₂ hb₁
-/
private lemma antisymm_aux (hst : toColex s <= toColex t) (hts : toColex t <= toColex s) : s subseteq t := by
  intro a has
  by_contra hat
  have ⟨_b, hb₁, hb₂, _⟩ := trans_aux hst hts has hat
  exact hb₂ hb₁

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder (Colex (Finset α)) where
  body: (ha' ha).elim
  le_antisymm _ _ hst hts := (antisymm_aux hst hts).antisymm (antisymm_aux hts hst)
  le_trans s t u hst htu a has hau := by
    by_cases hat : a in ofColex t
    · have ⟨b, hbu, hbt, hab⟩ := htu hat hau
      by_cases hbs : b in ofColex s
      · have ⟨c, hcu, hcs, hbc⟩ := trans_aux h

中文:
实例 instPartialOrder
  签名: : 偏序 (Colex (有限集 α)) where
  定义体: (ha' ha).elim
  le_antisymm _ _ hst hts := (antisymm_aux hst hts).antisymm (antisymm_aux hts hst)
  le_trans s t u hst htu a has hau := by
    by_cases hat : a in ofColex t
    · have ⟨b, hbu, hbt, hab⟩ := htu hat hau
      by_cases hbs : b in ofColex s
      · have ⟨c, hcu, hcs, hbc⟩ := trans_aux h
-/
instance instPartialOrder : PartialOrder (Colex (Finset α)) where
  le_refl _ _ ha ha' := (ha' ha).elim
  le_antisymm _ _ hst hts := (antisymm_aux hst hts).antisymm (antisymm_aux hts hst)
  le_trans s t u hst htu a has hau := by
    by_cases hat : a in ofColex t
    · have ⟨b, hbu, hbt, hab⟩ := htu hat hau
      by_cases hbs : b in ofColex s
      · have ⟨c, hcu, hcs, hbc⟩ := trans_aux hst htu hbs hbt
        exact ⟨c, hcu, hcs, hab.trans hbc⟩
      · exact ⟨b, hbu, hbs, hab⟩
    · exact trans_aux hst htu has hat

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  given: {s t : Colex (Finset α)}
  proof: Iff.rfl

中文:
引理 le_def
  条件: {s t : Colex (有限集 α)}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_def {s t : Colex (Finset α)} :
    s <= t ↔ forall ⦃a⦄, a in ofColex s -> a ∉ ofColex t -> exists b, b in ofColex t ∧ b ∉ ofColex s ∧ a <= b :=
  Iff.rfl

/--
lemma `toColex_le_toColex` / 引理 `toColex_le_toColex`

English:
lemma toColex_le_toColex
  proof: Iff.rfl

中文:
引理 toColex_le_toColex
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma toColex_le_toColex :
    toColex s <= toColex t ↔ forall ⦃a⦄, a in s -> a ∉ t -> exists b, b in t ∧ b ∉ s ∧ a <= b := Iff.rfl

/--
lemma `toColex_lt_toColex` / 引理 `toColex_lt_toColex`

English:
lemma toColex_lt_toColex
  proof: by
  simp [lt_iff_le_and_ne, toColex_le_toColex, and_comm]

中文:
引理 toColex_lt_toColex
  证明: by
  simp [lt_iff_le_and_ne, toColex_le_toColex, and_comm]

Depends on / 依赖: and_comm, lt_iff_le_and_ne, toColex_le_toColex
-/
lemma toColex_lt_toColex :
    toColex s < toColex t ↔ s != t ∧ forall ⦃a⦄, a in s -> a ∉ t -> exists b, b in t ∧ b ∉ s ∧ a <= b := by
  simp [lt_iff_le_and_ne, toColex_le_toColex, and_comm]

/--
lemma `toColex_mono` / 引理 `toColex_mono`

English:
lemma toColex_mono
  statement: Monotone (@toColex (Finset α))
  proof: fun _s _t hst _a has hat => (hat <| hst has).elim

中文:
引理 toColex_mono
  结论: 递增 (@toColex (有限集 α))
  证明: fun _s _t hst _a has hat => (hat <| hst has).elim
-/
lemma toColex_mono : Monotone (@toColex (Finset α)) :=
  fun _s _t hst _a has hat => (hat <| hst has).elim

/--
lemma `toColex_strictMono` / 引理 `toColex_strictMono`

English:
lemma toColex_strictMono
  statement: StrictMono (@toColex (Finset α))
  proof: toColex_mono.strictMono_of_injective toColex.injective

中文:
引理 toColex_strictMono
  结论: 严格递增 (@toColex (有限集 α))
  证明: toColex_mono.strictMono_of_injective toColex.injective

Depends on / 依赖: injective, strictMono_of_injective, toColex, toColex.injective, toColex_mono, toColex_mono.strictMono_of_injective
-/
lemma toColex_strictMono : StrictMono (@toColex (Finset α)) :=
  toColex_mono.strictMono_of_injective toColex.injective

/--
lemma `toColex_le_toColex_of_subset` / 引理 `toColex_le_toColex_of_subset`

English:
lemma toColex_le_toColex_of_subset
  given: (h : s subseteq t)
  statement: toColex s <= toColex t
  proof: toColex_mono h

中文:
引理 toColex_le_toColex_of_subset
  条件: (h : s subseteq t)
  结论: toColex s <= toColex t
  证明: toColex_mono h

Depends on / 依赖: toColex_mono
-/
lemma toColex_le_toColex_of_subset (h : s subseteq t) : toColex s <= toColex t := toColex_mono h

/--
lemma `toColex_lt_toColex_of_ssubset` / 引理 `toColex_lt_toColex_of_ssubset`

English:
lemma toColex_lt_toColex_of_ssubset
  given: (h : s ⊂ t)
  statement: toColex s < toColex t
  proof: toColex_strictMono h

中文:
引理 toColex_lt_toColex_of_ssubset
  条件: (h : s ⊂ t)
  结论: toColex s < toColex t
  证明: toColex_strictMono h

Depends on / 依赖: toColex_strictMono
-/
lemma toColex_lt_toColex_of_ssubset (h : s ⊂ t) : toColex s < toColex t := toColex_strictMono h

/--
Instance `instOrderBot` / 实例 `instOrderBot`

English:
instance instOrderBot
  signature: : OrderBot (Colex (Finset α)) where
  body: toColex ∅
  bot_le s a ha := by cases ha

中文:
实例 instOrderBot
  签名: : 有底序 (Colex (有限集 α)) where
  定义体: toColex ∅
  bot_le s a ha := by cases ha

Depends on / 依赖: toColex
-/
instance instOrderBot : OrderBot (Colex (Finset α)) where
  bot := toColex ∅
  bot_le s a ha := by cases ha

/--
lemma `toColex_empty` / 引理 `toColex_empty`

English:
lemma toColex_empty
  statement: toColex (∅ : Finset α) = ⊥
  proof: rfl

中文:
引理 toColex_empty
  结论: toColex (∅ : 有限集 α) = ⊥
  证明: rfl
-/
@[simp] lemma toColex_empty : toColex (∅ : Finset α) = ⊥ := rfl
/--
lemma `ofColex_bot` / 引理 `ofColex_bot`

English:
lemma ofColex_bot
  statement: ofColex (⊥ : Colex (Finset α)) = ∅
  proof: rfl

中文:
引理 ofColex_bot
  结论: ofColex (⊥ : Colex (有限集 α)) = ∅
  证明: rfl
-/
@[simp] lemma ofColex_bot : ofColex (⊥ : Colex (Finset α)) = ∅ := rfl

/--
lemma `forall_le_mono` / 引理 `forall_le_mono`

English:
lemma forall_le_mono
  given: (hst : toColex s <= toColex t) (ht : forall b in t, b <= a)
  statement: forall b in s, b <= a
  proof: by
  rintro b hb
  by_cases b in t
  · exact ht _ ‹_›
  · obtain ⟨c, hct, -, hbc⟩ := hst hb ‹_›
exact hbc.trans ht _ hct

中文:
引理 对任意_le_mono
  条件: (hst : toColex s <= toColex t) (ht : 对任意 b in t, b <= a)
  结论: 对任意 b in s, b <= a
  证明: by
  rintro b hb
  by_cases b in t
  · exact ht _ ‹_›
  · obtain ⟨c, hct, -, hbc⟩ := hst hb ‹_›
exact hbc.trans ht _ hct

Depends on / 依赖: hbc.trans, instFintypeProd
-/
lemma forall_le_mono (hst : toColex s <= toColex t) (ht : forall b in t, b <= a) : forall b in s, b <= a := by
  rintro b hb
  by_cases b in t
  · exact ht _ ‹_›
  · obtain ⟨c, hct, -, hbc⟩ := hst hb ‹_›
exact hbc.trans ht _ hct

/--
lemma `forall_lt_mono` / 引理 `forall_lt_mono`

English:
lemma forall_lt_mono
  given: (hst : toColex s <= toColex t) (ht : forall b in t, b < a)
  statement: forall b in s, b < a
  proof: by
  rintro b hb
  by_cases b in t
  · exact ht _ ‹_›
  · obtain ⟨c, hct, -, hbc⟩ := hst hb ‹_›
exact hbc.trans_lt ht _ hct

中文:
引理 对任意_lt_mono
  条件: (hst : toColex s <= toColex t) (ht : 对任意 b in t, b < a)
  结论: 对任意 b in s, b < a
  证明: by
  rintro b hb
  by_cases b in t
  · exact ht _ ‹_›
  · obtain ⟨c, hct, -, hbc⟩ := hst hb ‹_›
exact hbc.trans_lt ht _ hct

Depends on / 依赖: hbc.trans_lt, trans_lt
-/
lemma forall_lt_mono (hst : toColex s <= toColex t) (ht : forall b in t, b < a) : forall b in s, b < a := by
  rintro b hb
  by_cases b in t
  · exact ht _ ‹_›
  · obtain ⟨c, hct, -, hbc⟩ := hst hb ‹_›
exact hbc.trans_lt ht _ hct

/--
lemma `toColex_le_singleton` / 引理 `toColex_le_singleton`

English:
lemma toColex_le_singleton
  statement: toColex s <= toColex {a} ↔ forall b in s, b <= a ∧ (a in s -> b = a)
  proof: by
  simp only [toColex_le_toColex, mem_singleton, exists_eq_left]
  refine forall₂_congr fun b _ => ?_; obtain rfl | hba := eq_or_ne b a <;> aesop

中文:
引理 toColex_le_singleton
  结论: toColex s <= toColex {a} ↔ 对任意 b in s, b <= a ∧ (a in s -> b = a)
  证明: by
  simp only [toColex_le_toColex, mem_singleton, exists_eq_left]
  refine forall₂_congr fun b _ => ?_; obtain rfl | hba := eq_or_ne b a <;> aesop

Depends on / 依赖: eq_or_ne, exists_eq_left, mem_singleton, toColex_le_toColex
-/
lemma toColex_le_singleton : toColex s <= toColex {a} ↔ forall b in s, b <= a ∧ (a in s -> b = a) := by
  simp only [toColex_le_toColex, mem_singleton, exists_eq_left]
  refine forall₂_congr fun b _ => ?_; obtain rfl | hba := eq_or_ne b a <;> aesop

/--
lemma `toColex_lt_singleton` / 引理 `toColex_lt_singleton`

English:
lemma toColex_lt_singleton
  statement: toColex s < toColex {a} ↔ forall b in s, b < a
  proof: by
  rw [lt_iff_le_and_ne]; rw [toColex_le_singleton]; rw [ne_eq]; rw [toColex_inj]
  refine ⟨fun h b hb => (h.1 _ hb).1.lt_of_ne ?_,
    fun h => ⟨fun b hb => ⟨(h _ hb).le, fun ha => (lt_irrefl _ <| h _ ha).elim⟩, ?_⟩⟩ <;> rintro rfl
· refine h.2 eq_singleton_iff_unique_mem.2 ⟨hb, fun c hc => (h.1 

中文:
引理 toColex_lt_singleton
  结论: toColex s < toColex {a} ↔ 对任意 b in s, b < a
  证明: by
  rw [lt_iff_le_and_ne]; rw [toColex_le_singleton]; rw [ne_eq]; rw [toColex_inj]
  refine ⟨fun h b hb => (h.1 _ hb).1.lt_of_ne ?_,
    fun h => ⟨fun b hb => ⟨(h _ hb).le, fun ha => (lt_irrefl _ <| h _ ha).elim⟩, ?_⟩⟩ <;> rintro rfl
· refine h.2 eq_singleton_iff_unique_mem.2 ⟨hb, fun c hc => (h.1 

Depends on / 依赖: eq_singleton_iff_unique_mem, lt_iff_le_and_ne, lt_irrefl, lt_of_ne, ne_eq, toColex_inj, toColex_le_singleton
-/
lemma toColex_lt_singleton : toColex s < toColex {a} ↔ forall b in s, b < a := by
  rw [lt_iff_le_and_ne]; rw [toColex_le_singleton]; rw [ne_eq]; rw [toColex_inj]
  refine ⟨fun h b hb => (h.1 _ hb).1.lt_of_ne ?_,
    fun h => ⟨fun b hb => ⟨(h _ hb).le, fun ha => (lt_irrefl _ <| h _ ha).elim⟩, ?_⟩⟩ <;> rintro rfl
· refine h.2 eq_singleton_iff_unique_mem.2 ⟨hb, fun c hc => (h.1 _ hc).2 hb⟩
  · simp at h

/--
lemma `singleton_le_toColex` / 引理 `singleton_le_toColex`

English:
lemma singleton_le_toColex
  statement: (toColex {a} : Colex (Finset α)) <= toColex s ↔ exists x in s, a <= x
  proof: by
  simp [toColex_le_toColex]; by_cases a in s <;> aesop

中文:
引理 singleton_le_toColex
  结论: (toColex {a} : Colex (有限集 α)) <= toColex s ↔ 存在 x in s, a <= x
  证明: by
  simp [toColex_le_toColex]; by_cases a in s <;> aesop

Depends on / 依赖: toColex_le_toColex
-/
lemma singleton_le_toColex : (toColex {a} : Colex (Finset α)) <= toColex s ↔ exists x in s, a <= x := by
  simp [toColex_le_toColex]; by_cases a in s <;> aesop

/--
lemma `singleton_le_singleton` / 引理 `singleton_le_singleton`

English:
lemma singleton_le_singleton
  statement: (toColex ({a} : Finset α)) <= toColex {b} ↔ a <= b
  proof: by
  simp [toColex_le_singleton, eq_comm]

中文:
引理 singleton_le_singleton
  结论: (toColex ({a} : 有限集 α)) <= toColex {b} ↔ a <= b
  证明: by
  simp [toColex_le_singleton, eq_comm]

Depends on / 依赖: eq_comm, toColex_le_singleton
-/
lemma singleton_le_singleton : (toColex ({a} : Finset α)) <= toColex {b} ↔ a <= b := by
  simp [toColex_le_singleton, eq_comm]

/--
lemma `singleton_lt_singleton` / 引理 `singleton_lt_singleton`

English:
lemma singleton_lt_singleton
  statement: (toColex ({a} : Finset α)) < toColex {b} ↔ a < b
  proof: by
  simp [toColex_lt_singleton]

中文:
引理 singleton_lt_singleton
  结论: (toColex ({a} : 有限集 α)) < toColex {b} ↔ a < b
  证明: by
  simp [toColex_lt_singleton]

Depends on / 依赖: toColex_lt_singleton
-/
lemma singleton_lt_singleton : (toColex ({a} : Finset α)) < toColex {b} ↔ a < b := by
  simp [toColex_lt_singleton]

/--
lemma `le_iff_sdiff_subset_lowerClosure` / 引理 `le_iff_sdiff_subset_lowerClosure`

English:
lemma le_iff_sdiff_subset_lowerClosure
  given: {s t : Colex (Finset α)}
  proof: by
  simp [le_def, Set.subset_def, and_assoc]

中文:
引理 le_iff_sdiff_subset_lowerClosure
  条件: {s t : Colex (有限集 α)}
  证明: by
  simp [le_def, Set.subset_def, and_assoc]

Depends on / 依赖: Set.subset_def, and_assoc, le_def, subset_def
-/
lemma le_iff_sdiff_subset_lowerClosure {s t : Colex (Finset α)} :
    s <= t ↔ (↑(ofColex s) : Set α) \ ↑(ofColex t) subseteq
      lowerClosure (↑(ofColex t) \ ↑(ofColex s) : Set α) := by
  simp [le_def, Set.subset_def, and_assoc]

section DecidableEq
variable [DecidableEq α]

/--
Instance `instDecidableLE` / 实例 `instDecidableLE`

English:
instance instDecidableLE
  signature: [DecidableLE α]
  body: fun s t => decidable_of_iff'
    (forall ⦃a⦄, a in ofColex s -> a ∉ ofColex t -> exists b, b in ofColex t ∧ b ∉ ofColex s ∧ a <= b) Iff.rfl

中文:
实例 instDecidableLE
  签名: [DecidableLE α]
  定义体: fun s t => decidable_of_iff'
    (forall ⦃a⦄, a in ofColex s -> a ∉ ofColex t -> exists b, b in ofColex t ∧ b ∉ ofColex s ∧ a <= b) Iff.rfl

Depends on / 依赖: Iff.rfl, decidable_of_iff, ofColex
-/
instance instDecidableLE [DecidableLE α] : DecidableLE (Colex (Finset α)) :=
  fun s t => decidable_of_iff'
    (forall ⦃a⦄, a in ofColex s -> a ∉ ofColex t -> exists b, b in ofColex t ∧ b ∉ ofColex s ∧ a <= b) Iff.rfl

/--
Instance `instDecidableLT` / 实例 `instDecidableLT`

English:
instance instDecidableLT
  signature: [DecidableLE α]
  body: decidableLTOfDecidableLE

中文:
实例 instDecidableLT
  签名: [DecidableLE α]
  定义体: decidableLTOfDecidableLE

Depends on / 依赖: decidableLTOfDecidableLE
-/
instance instDecidableLT [DecidableLE α] : DecidableLT (Colex (Finset α)) :=
  decidableLTOfDecidableLE

/--
lemma `toColex_sdiff_le_toColex_sdiff` / 引理 `toColex_sdiff_le_toColex_sdiff`

English:
lemma toColex_sdiff_le_toColex_sdiff
  given: (hus : u subseteq s) (hut : u subseteq t)
  proof: by
  simp_rw [toColex_le_toColex, ← and_imp, ← and_assoc, ← mem_sdiff,
    sdiff_sdiff_sdiff_cancel_right (show u <= s from hus),
    sdiff_sdiff_sdiff_cancel_right (show u <= t from hut)]

中文:
引理 toColex_sdiff_le_toColex_sdiff
  条件: (hus : u subseteq s) (hut : u subseteq t)
  证明: by
  simp_rw [toColex_le_toColex, ← and_imp, ← and_assoc, ← mem_sdiff,
    sdiff_sdiff_sdiff_cancel_right (show u <= s from hus),
    sdiff_sdiff_sdiff_cancel_right (show u <= t from hut)]

Depends on / 依赖: and_assoc, and_imp, mem_sdiff, sdiff_sdiff_sdiff_cancel_right, simp_rw, toColex_le_toColex
-/
lemma toColex_sdiff_le_toColex_sdiff (hus : u subseteq s) (hut : u subseteq t) :
    toColex (s \ u) <= toColex (t \ u) ↔ toColex s <= toColex t := by
  simp_rw [toColex_le_toColex, ← and_imp, ← and_assoc, ← mem_sdiff,
    sdiff_sdiff_sdiff_cancel_right (show u <= s from hus),
    sdiff_sdiff_sdiff_cancel_right (show u <= t from hut)]

/--
lemma `toColex_sdiff_lt_toColex_sdiff` / 引理 `toColex_sdiff_lt_toColex_sdiff`

English:
lemma toColex_sdiff_lt_toColex_sdiff
  given: (hus : u subseteq s) (hut : u subseteq t)
  proof: lt_iff_lt_of_le_iff_le' (toColex_sdiff_le_toColex_sdiff hut hus)
    toColex_sdiff_le_toColex_sdiff hus hut

中文:
引理 toColex_sdiff_lt_toColex_sdiff
  条件: (hus : u subseteq s) (hut : u subseteq t)
  证明: lt_iff_lt_of_le_iff_le' (toColex_sdiff_le_toColex_sdiff hut hus)
    toColex_sdiff_le_toColex_sdiff hus hut

Depends on / 依赖: lt_iff_lt_of_le_iff_le, toColex_sdiff_le_toColex_sdiff
-/
lemma toColex_sdiff_lt_toColex_sdiff (hus : u subseteq s) (hut : u subseteq t) :
    toColex (s \ u) < toColex (t \ u) ↔ toColex s < toColex t :=
lt_iff_lt_of_le_iff_le' (toColex_sdiff_le_toColex_sdiff hut hus)
    toColex_sdiff_le_toColex_sdiff hus hut

/--
lemma `toColex_sdiff_le_toColex_sdiff'` / 引理 `toColex_sdiff_le_toColex_sdiff'`

English:
lemma toColex_sdiff_le_toColex_sdiff'
  proof: by
  simpa using toColex_sdiff_le_toColex_sdiff (inter_subset_left (s₁ := s)) inter_subset_right

中文:
引理 toColex_sdiff_le_toColex_sdiff'
  证明: by
  simpa using toColex_sdiff_le_toColex_sdiff (inter_subset_left (s₁ := s)) inter_subset_right
-/
@[simp] lemma toColex_sdiff_le_toColex_sdiff' :
    toColex (s \ t) <= toColex (t \ s) ↔ toColex s <= toColex t := by
  simpa using toColex_sdiff_le_toColex_sdiff (inter_subset_left (s₁ := s)) inter_subset_right

/--
lemma `toColex_sdiff_lt_toColex_sdiff'` / 引理 `toColex_sdiff_lt_toColex_sdiff'`

English:
lemma toColex_sdiff_lt_toColex_sdiff'
  proof: by
  simpa using toColex_sdiff_lt_toColex_sdiff (inter_subset_left (s₁ := s)) inter_subset_right

中文:
引理 toColex_sdiff_lt_toColex_sdiff'
  证明: by
  simpa using toColex_sdiff_lt_toColex_sdiff (inter_subset_left (s₁ := s)) inter_subset_right
-/
@[simp] lemma toColex_sdiff_lt_toColex_sdiff' :
    toColex (s \ t) < toColex (t \ s) ↔ toColex s < toColex t := by
  simpa using toColex_sdiff_lt_toColex_sdiff (inter_subset_left (s₁ := s)) inter_subset_right

end DecidableEq

/--
lemma `cons_le_cons` / 引理 `cons_le_cons`

English:
lemma cons_le_cons
  given: (ha hb)
  statement: toColex (s.cons a ha) <= toColex (s.cons b hb) ↔ a <= b
  proof: by
  obtain rfl | hab := eq_or_ne a b
  · simp
  classical
  rw [← toColex_sdiff_le_toColex_sdiff']; rw [cons_sdiff_cons hab]; rw [cons_sdiff_cons hab.symm]; rw [singleton_le_singleton]

中文:
引理 cons_le_cons
  条件: (ha hb)
  结论: toColex (s.cons a ha) <= toColex (s.cons b hb) ↔ a <= b
  证明: by
  obtain rfl | hab := eq_or_ne a b
  · simp
  classical
  rw [← toColex_sdiff_le_toColex_sdiff']; rw [cons_sdiff_cons hab]; rw [cons_sdiff_cons hab.symm]; rw [singleton_le_singleton]
-/
@[simp] lemma cons_le_cons (ha hb) : toColex (s.cons a ha) <= toColex (s.cons b hb) ↔ a <= b := by
  obtain rfl | hab := eq_or_ne a b
  · simp
  classical
  rw [← toColex_sdiff_le_toColex_sdiff']; rw [cons_sdiff_cons hab]; rw [cons_sdiff_cons hab.symm]; rw [singleton_le_singleton]

/--
lemma `cons_lt_cons` / 引理 `cons_lt_cons`

English:
lemma cons_lt_cons
  given: (ha hb)
  statement: toColex (s.cons a ha) < toColex (s.cons b hb) ↔ a < b
  proof: lt_iff_lt_of_le_iff_le' (cons_le_cons _ _) (cons_le_cons _ _)

中文:
引理 cons_lt_cons
  条件: (ha hb)
  结论: toColex (s.cons a ha) < toColex (s.cons b hb) ↔ a < b
  证明: lt_iff_lt_of_le_iff_le' (cons_le_cons _ _) (cons_le_cons _ _)
-/
@[simp] lemma cons_lt_cons (ha hb) : toColex (s.cons a ha) < toColex (s.cons b hb) ↔ a < b :=
  lt_iff_lt_of_le_iff_le' (cons_le_cons _ _) (cons_le_cons _ _)

variable [DecidableEq α]

/--
lemma `insert_le_insert` / 引理 `insert_le_insert`

English:
lemma insert_le_insert
  given: (ha : a ∉ s) (hb : b ∉ s)
  proof: by
  rw [← cons_eq_insert _ _ ha]; rw [← cons_eq_insert _ _ hb]; rw [cons_le_cons]

中文:
引理 insert_le_insert
  条件: (ha : a ∉ s) (hb : b ∉ s)
  证明: by
  rw [← cons_eq_insert _ _ ha]; rw [← cons_eq_insert _ _ hb]; rw [cons_le_cons]

Depends on / 依赖: cons_eq_insert, cons_le_cons
-/
lemma insert_le_insert (ha : a ∉ s) (hb : b ∉ s) :
    toColex (insert a s) <= toColex (insert b s) ↔ a <= b := by
  rw [← cons_eq_insert _ _ ha]; rw [← cons_eq_insert _ _ hb]; rw [cons_le_cons]

/--
lemma `insert_lt_insert` / 引理 `insert_lt_insert`

English:
lemma insert_lt_insert
  given: (ha : a ∉ s) (hb : b ∉ s)
  proof: by
  rw [← cons_eq_insert _ _ ha]; rw [← cons_eq_insert _ _ hb]; rw [cons_lt_cons]

中文:
引理 insert_lt_insert
  条件: (ha : a ∉ s) (hb : b ∉ s)
  证明: by
  rw [← cons_eq_insert _ _ ha]; rw [← cons_eq_insert _ _ hb]; rw [cons_lt_cons]

Depends on / 依赖: cons_eq_insert, cons_lt_cons
-/
lemma insert_lt_insert (ha : a ∉ s) (hb : b ∉ s) :
    toColex (insert a s) < toColex (insert b s) ↔ a < b := by
  rw [← cons_eq_insert _ _ ha]; rw [← cons_eq_insert _ _ hb]; rw [cons_lt_cons]

/--
lemma `erase_le_erase` / 引理 `erase_le_erase`

English:
lemma erase_le_erase
  given: (ha : a in s) (hb : b in s)
  proof: by
  obtain rfl | hab := eq_or_ne a b
  · simp
  rw [← toColex_sdiff_le_toColex_sdiff']; rw [erase_sdiff_erase hab hb]; rw [erase_sdiff_erase hab.symm ha]; rw [singleton_le_singleton]

中文:
引理 erase_le_erase
  条件: (ha : a in s) (hb : b in s)
  证明: by
  obtain rfl | hab := eq_or_ne a b
  · simp
  rw [← toColex_sdiff_le_toColex_sdiff']; rw [erase_sdiff_erase hab hb]; rw [erase_sdiff_erase hab.symm ha]; rw [singleton_le_singleton]

Depends on / 依赖: eq_or_ne, erase_sdiff_erase, hab.symm, singleton_le_singleton, toColex_sdiff_le_toColex_sdiff
-/
lemma erase_le_erase (ha : a in s) (hb : b in s) :
    toColex (s.erase a) <= toColex (s.erase b) ↔ b <= a := by
  obtain rfl | hab := eq_or_ne a b
  · simp
  rw [← toColex_sdiff_le_toColex_sdiff']; rw [erase_sdiff_erase hab hb]; rw [erase_sdiff_erase hab.symm ha]; rw [singleton_le_singleton]

/--
lemma `erase_lt_erase` / 引理 `erase_lt_erase`

English:
lemma erase_lt_erase
  given: (ha : a in s) (hb : b in s)
  proof: lt_iff_lt_of_le_iff_le' (erase_le_erase hb ha) (erase_le_erase ha hb)

中文:
引理 erase_lt_erase
  条件: (ha : a in s) (hb : b in s)
  证明: lt_iff_lt_of_le_iff_le' (erase_le_erase hb ha) (erase_le_erase ha hb)

Depends on / 依赖: erase_le_erase, lt_iff_lt_of_le_iff_le
-/
lemma erase_lt_erase (ha : a in s) (hb : b in s) :
    toColex (s.erase a) < toColex (s.erase b) ↔ b < a :=
  lt_iff_lt_of_le_iff_le' (erase_le_erase hb ha) (erase_le_erase ha hb)

end PartialOrder

variable [LinearOrder α] [LinearOrder β] {f : α -> β} {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)}
  {s t u : Finset α} {a b : α} {r : Nat}

/--
Instance `instLinearOrder` / 实例 `instLinearOrder`

English:
instance instLinearOrder
  signature: : LinearOrder (Colex (Finset α)) where
  body: by
    obtain rfl | hts := eq_or_ne t s
    · simp
    have ⟨a, ha, hamax⟩ := exists_max_image _ id
      (symmDiff_nonempty.2 <| ofColex.injective.ne_iff.2 hts)
    simp_rw [mem_symmDiff] at ha hamax
    exact ha.imp (fun ha b hbs hbt => ⟨a, ha.1, ha.2, hamax _ <| Or.inr ⟨hbs, hbt⟩⟩)
      (fun ha 

中文:
实例 instLinearOrder
  签名: : 线性序 (Colex (有限集 α)) where
  定义体: by
    obtain rfl | hts := eq_or_ne t s
    · simp
    have ⟨a, ha, hamax⟩ := exists_max_image _ id
      (symmDiff_nonempty.2 <| ofColex.injective.ne_iff.2 hts)
    simp_rw [mem_symmDiff] at ha hamax
    exact ha.imp (fun ha b hbs hbt => ⟨a, ha.1, ha.2, hamax _ <| Or.inr ⟨hbs, hbt⟩⟩)
      (fun ha 

Depends on / 依赖: Or.inl, Or.inr, eq_or_ne, exists_max_image, ha.imp, injective, instDecidableLE, instDecidableLT, mem_symmDiff, ne_iff, ofColex, ofColex.injective.ne_iff, simp_rw, symmDiff_nonempty, toDecidableLE, toDecidableLT
-/
instance instLinearOrder : LinearOrder (Colex (Finset α)) where
  le_total s t := by
    obtain rfl | hts := eq_or_ne t s
    · simp
    have ⟨a, ha, hamax⟩ := exists_max_image _ id
      (symmDiff_nonempty.2 <| ofColex.injective.ne_iff.2 hts)
    simp_rw [mem_symmDiff] at ha hamax
    exact ha.imp (fun ha b hbs hbt => ⟨a, ha.1, ha.2, hamax _ <| Or.inr ⟨hbs, hbt⟩⟩)
      (fun ha b hbt hbs => ⟨a, ha.1, ha.2, hamax _ <| Or.inl ⟨hbt, hbs⟩⟩)
  toDecidableLE := instDecidableLE
  toDecidableLT := instDecidableLT

open scoped symmDiff

set_option backward.privateInPublic true in
/--
lemma `max_mem_aux` / 引理 `max_mem_aux`

English:
lemma max_mem_aux
  given: {s t : Colex (Finset α)} (hst : s != t)
  proof: by
  simpa

中文:
引理 max_mem_aux
  条件: {s t : Colex (有限集 α)} (hst : s != t)
  证明: by
  simpa
-/
private lemma max_mem_aux {s t : Colex (Finset α)} (hst : s != t) :
    (ofColex s ∆ ofColex t).Nonempty := by
  simpa

/--
lemma `toColex_lt_toColex_iff_exists_forall_lt` / 引理 `toColex_lt_toColex_iff_exists_forall_lt`

English:
lemma toColex_lt_toColex_iff_exists_forall_lt
  proof: by
  rw [← not_le]; rw [toColex_le_toColex]; rw [not_forall]
  simp only [not_forall, not_exists, not_and, not_le, exists_prop]

中文:
引理 toColex_lt_toColex_iff_存在_对任意_lt
  证明: by
  rw [← not_le]; rw [toColex_le_toColex]; rw [not_forall]
  simp only [not_forall, not_exists, not_and, not_le, exists_prop]

Depends on / 依赖: exists_prop, not_and, not_exists, not_forall, not_le, toColex_le_toColex
-/
lemma toColex_lt_toColex_iff_exists_forall_lt :
    toColex s < toColex t ↔ exists a in t, a ∉ s ∧ forall b in s, b ∉ t -> b < a := by
  rw [← not_le]; rw [toColex_le_toColex]; rw [not_forall]
  simp only [not_forall, not_exists, not_and, not_le, exists_prop]

/--
lemma `lt_iff_exists_forall_lt` / 引理 `lt_iff_exists_forall_lt`

English:
lemma lt_iff_exists_forall_lt
  given: {s t : Colex (Finset α)}
  proof: toColex_lt_toColex_iff_exists_forall_lt

中文:
引理 lt_iff_存在_对任意_lt
  条件: {s t : Colex (有限集 α)}
  证明: toColex_lt_toColex_iff_exists_forall_lt

Depends on / 依赖: toColex_lt_toColex_iff_exists_forall_lt
-/
lemma lt_iff_exists_forall_lt {s t : Colex (Finset α)} :
    s < t ↔ exists a in ofColex t, a ∉ ofColex s ∧ forall b in ofColex s, b ∉ ofColex t -> b < a :=
  toColex_lt_toColex_iff_exists_forall_lt

/--
lemma `toColex_le_toColex_iff_max'_mem` / 引理 `toColex_le_toColex_iff_max'_mem`

English:
lemma toColex_le_toColex_iff_max'_mem
  proof: by
  refine ⟨fun h hst => ?_, fun h a has hat => ?_⟩
  · set m := (s ∆ t).max' (symmDiff_nonempty.2 hst)
    by_contra hmt
    have hms : m in s := by
simpa [m, mem_symmDiff, hmt] using max'_mem _ symmDiff_nonempty.2 hst
    have ⟨b, hbt, hbs, hmb⟩ := h hms hmt
exact lt_irrefl _ (max'_lt_iff _ _).1 

中文:
引理 toColex_le_toColex_iff_max'_mem
  证明: by
  refine ⟨fun h hst => ?_, fun h a has hat => ?_⟩
  · set m := (s ∆ t).max' (symmDiff_nonempty.2 hst)
    by_contra hmt
    have hms : m in s := by
simpa [m, mem_symmDiff, hmt] using max'_mem _ symmDiff_nonempty.2 hst
    have ⟨b, hbt, hbs, hmb⟩ := h hms hmt
exact lt_irrefl _ (max'_lt_iff _ _).1 

Depends on / 依赖: Or.inl, Or.inr, _lt_iff, _mem, hmb.lt_of_ne, le_max, lt_irrefl, lt_of_ne, mem_sy, mem_symmDiff, ne_of_mem_of_not_mem, symmDiff_nonempty
-/
lemma toColex_le_toColex_iff_max'_mem :
    toColex s <= toColex t ↔ forall hst : s != t, (s ∆ t).max' (symmDiff_nonempty.2 hst) in t := by
  refine ⟨fun h hst => ?_, fun h a has hat => ?_⟩
  · set m := (s ∆ t).max' (symmDiff_nonempty.2 hst)
    by_contra hmt
    have hms : m in s := by
simpa [m, mem_symmDiff, hmt] using max'_mem _ symmDiff_nonempty.2 hst
    have ⟨b, hbt, hbs, hmb⟩ := h hms hmt
exact lt_irrefl _ (max'_lt_iff _ _).1 (hmb.lt_of_ne <| ne_of_mem_of_not_mem hms hbs) _
mem_symmDiff.2 Or.inr ⟨hbt, hbs⟩
  · have hst : s != t := ne_of_mem_of_not_mem' has hat
refine ⟨_, h hst, ?_, le_max' _ _ mem_symmDiff.2 Or.inl ⟨has, hat⟩⟩
simpa [mem_symmDiff, h hst] using max'_mem _ symmDiff_nonempty.2 hst

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `le_iff_max'_mem` / 引理 `le_iff_max'_mem`

English:
lemma le_iff_max'_mem
  given: {s t : Colex (Finset α)}
  proof: toColex_le_toColex_iff_max'_mem

中文:
引理 le_iff_max'_mem
  条件: {s t : Colex (有限集 α)}
  证明: toColex_le_toColex_iff_max'_mem

Depends on / 依赖: _mem, toColex_le_toColex_iff_max
-/
lemma le_iff_max'_mem {s t : Colex (Finset α)} :
    s <= t ↔ forall h : s != t, (ofColex s ∆ ofColex t).max' (max_mem_aux h) in ofColex t :=
  toColex_le_toColex_iff_max'_mem

/--
lemma `toColex_lt_toColex_iff_max'_mem` / 引理 `toColex_lt_toColex_iff_max'_mem`

English:
lemma toColex_lt_toColex_iff_max'_mem
  proof: by
  rw [lt_iff_le_and_ne]; rw [toColex_le_toColex_iff_max'_mem]; aesop

中文:
引理 toColex_lt_toColex_iff_max'_mem
  证明: by
  rw [lt_iff_le_and_ne]; rw [toColex_le_toColex_iff_max'_mem]; aesop

Depends on / 依赖: _mem, lt_iff_le_and_ne, toColex_le_toColex_iff_max
-/
lemma toColex_lt_toColex_iff_max'_mem :
    toColex s < toColex t ↔ exists hst : s != t, (s ∆ t).max' (symmDiff_nonempty.2 hst) in t := by
  rw [lt_iff_le_and_ne]; rw [toColex_le_toColex_iff_max'_mem]; aesop

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `lt_iff_max'_mem` / 引理 `lt_iff_max'_mem`

English:
lemma lt_iff_max'_mem
  given: {s t : Colex (Finset α)}
  proof: by
  rw [lt_iff_le_and_ne]; rw [le_iff_max'_mem]; aesop

中文:
引理 lt_iff_max'_mem
  条件: {s t : Colex (有限集 α)}
  证明: by
  rw [lt_iff_le_and_ne]; rw [le_iff_max'_mem]; aesop

Depends on / 依赖: _mem, le_iff_max, lt_iff_le_and_ne
-/
lemma lt_iff_max'_mem {s t : Colex (Finset α)} :
    s < t ↔ exists h : s != t, (ofColex s ∆ ofColex t).max' (max_mem_aux h) in ofColex t := by
  rw [lt_iff_le_and_ne]; rw [le_iff_max'_mem]; aesop

/--
lemma `lt_iff_exists_filter_lt` / 引理 `lt_iff_exists_filter_lt`

English:
lemma lt_iff_exists_filter_lt
  proof: by
  simp only [lt_iff_exists_forall_lt, mem_sdiff, filter_inj, and_assoc]
  refine ⟨fun h => ?_, ?_⟩
  · let u := {w in t \ s | forall a in s, a ∉ t -> a < w}
    have mem_u {w : α} : w in u ↔ w in t ∧ w ∉ s ∧ forall a in s, a ∉ t -> a < w := by simp [u, and_assoc]
    have hu : u.Nonempty := h.imp

中文:
引理 lt_iff_存在_filter_lt
  证明: by
  simp only [lt_iff_exists_forall_lt, mem_sdiff, filter_inj, and_assoc]
  refine ⟨fun h => ?_, ?_⟩
  · let u := {w in t \ s | forall a in s, a ∉ t -> a < w}
    have mem_u {w : α} : w in u ↔ w in t ∧ w ∉ s ∧ forall a in s, a ∉ t -> a < w := by simp [u, and_assoc]
    have hu : u.Nonempty := h.imp

Depends on / 依赖: Nonempty, _mem, and_assoc, filter_inj, h.imp, hma.asymm, lt_iff_exists_forall_lt, mem_sdiff, mem_u, not_imp_comm, u.Nonempty
-/
lemma lt_iff_exists_filter_lt :
    toColex s < toColex t ↔ exists w in t \ s, {a in s | w < a} = {a in t | w < a} := by
  simp only [lt_iff_exists_forall_lt, mem_sdiff, filter_inj, and_assoc]
  refine ⟨fun h => ?_, ?_⟩
  · let u := {w in t \ s | forall a in s, a ∉ t -> a < w}
    have mem_u {w : α} : w in u ↔ w in t ∧ w ∉ s ∧ forall a in s, a ∉ t -> a < w := by simp [u, and_assoc]
    have hu : u.Nonempty := h.imp fun _ => mem_u.2
    let m := max' _ hu
have ⟨hmt, hms, hm⟩ : m in t ∧ m ∉ s ∧ forall a in s, a ∉ t -> a < m := mem_u.1 max'_mem _ _
    refine ⟨m, hmt, hms, fun a hma => ⟨fun has => not_imp_comm.1 (hm _ has) hma.asymm, fun hat => ?_⟩⟩
    by_contra has
    have hau : a in u := mem_u.2 ⟨hat, has, fun b hbs hbt => (hm _ hbs hbt).trans hma⟩
exact hma.not_ge le_max' _ _ hau
  · rintro ⟨w, hwt, hws, hw⟩
    refine ⟨w, hwt, hws, fun a has hat => ?_⟩
    by_contra! hwa
exact hat (hw <| hwa.lt_of_ne <| ne_of_mem_of_not_mem hwt hat).1 has

/--
lemma `erase_le_erase_min'` / 引理 `erase_le_erase_min'`

English:
lemma erase_le_erase_min'
  given: (hst : toColex s <= toColex t) (hcard : #s <= #t) (ha : a in s)
  proof: by
  generalize_proofs ht
  set m := min' t ht
  -- Case on whether `s = t`
  obtain rfl | h' := eq_or_ne s t
  -- If `s = t`, then `s \ {a} ≤ s \ {m}` because `m ≤ a`
· exact (erase_le_erase ha <| min'_mem _ _).2 min'_le _ _ ha
  -- If `s ≠ t`, call `w` the colex witness. Case on whether `w < a` or

中文:
引理 erase_le_erase_min'
  条件: (hst : toColex s <= toColex t) (hcard : #s <= #t) (ha : a in s)
  证明: by
  generalize_proofs ht
  set m := min' t ht
  -- Case on whether `s = t`
  obtain rfl | h' := eq_or_ne s t
  -- If `s = t`, then `s \ {a} ≤ s \ {m}` because `m ≤ a`
· exact (erase_le_erase ha <| min'_mem _ _).2 min'_le _ _ ha
  -- If `s ≠ t`, call `w` the colex witness. Case on whether `w < a` or

Depends on / 依赖: generalize_proofs
-/
lemma erase_le_erase_min' (hst : toColex s <= toColex t) (hcard : #s <= #t) (ha : a in s) :
    toColex (s.erase a) <=
      toColex (t.erase <| min' t <| card_pos.1 <| (card_pos.2 ⟨a, ha⟩).trans_le hcard) := by
  generalize_proofs ht
  set m := min' t ht
  -- Case on whether `s = t`
  obtain rfl | h' := eq_or_ne s t
  -- If `s = t`, then `s \ {a} ≤ s \ {m}` because `m ≤ a`
· exact (erase_le_erase ha <| min'_mem _ _).2 min'_le _ _ ha
  -- If `s ≠ t`, call `w` the colex witness. Case on whether `w < a` or `a < w`
replace hst := hst.lt_of_ne toColex_inj.not.2 h'
  simp only [lt_iff_exists_filter_lt, mem_sdiff, filter_inj, and_assoc] at hst
  obtain ⟨w, hwt, hws, hw⟩ := hst
  obtain hwa | haw := (ne_of_mem_of_not_mem ha hws).symm.lt_or_gt
  -- If `w < a`, then `a` is the colex witness for `s \ {a} < t \ {m}`
  · have hma : m < a := (min'_le _ _ hwt).trans_lt hwa
    refine (lt_iff_exists_forall_lt.2 ⟨a, mem_erase.2 ⟨hma.ne', (hw hwa).1 ha⟩,
      notMem_erase _ _, fun b hbs hbt => ?_⟩).le
    change b ∉ t.erase m at hbt
    rw [mem_erase]; rw [not_and_or]; rw [not_ne_iff] at hbt
    obtain rfl | hbt := hbt
    · assumption
    · by_contra! hab
exact hbt (hw <| hwa.trans_le hab).1 mem_of_mem_erase hbs
  -- If `a < w`, case on whether `m < w` or `m = w`
  obtain rfl | hmw : m = w ∨ m < w := (min'_le _ _ hwt).eq_or_lt
  -- If `m = w`, then `s \ {a} = t \ {m}`
  · have : erase t m subseteq erase s a := by
      rintro b hb
      rw [mem_erase] at hb ⊢
      exact ⟨(haw.trans_le <| min'_le _ _ hb.2).ne',
        (hw <| hb.1.lt_of_le' <| min'_le _ _ hb.2).2 hb.2⟩
    rw [eq_of_subset_of_card_le this]
    rw [card_erase_of_mem ha]; rw [card_erase_of_mem (min'_mem _ _)]
    exact tsub_le_tsub_right hcard _
  -- If `m < w`, then `w` works as the colex witness for `s \ {a} < t \ {m}`
  · refine (lt_iff_exists_forall_lt.2 ⟨w, mem_erase.2 ⟨hmw.ne', hwt⟩, mt mem_of_mem_erase hws,
      fun b hbs hbt => ?_⟩).le
    change b ∉ t.erase m at hbt
    rw [mem_erase]; rw [not_and_or]; rw [not_ne_iff] at hbt
    obtain rfl | hbt := hbt
    · assumption
    · by_contra! hwb
exact hbt (hw <| hwb.lt_of_ne <| ne_of_mem_of_not_mem hwt hbt).1 mem_of_mem_erase hbs

/--
lemma `toColex_image_le_toColex_image` / 引理 `toColex_image_le_toColex_image`

English:
lemma toColex_image_le_toColex_image
  given: (hf : StrictMono f)
  proof: by
  simp [toColex_le_toColex, hf.le_iff_le, hf.injective.eq_iff]

中文:
引理 toColex_image_le_toColex_image
  条件: (hf : 严格递增 f)
  证明: by
  simp [toColex_le_toColex, hf.le_iff_le, hf.injective.eq_iff]

Depends on / 依赖: eq_iff, hf.injective.eq_iff, hf.le_iff_le, injective, le_iff_le, toColex_le_toColex
-/
lemma toColex_image_le_toColex_image (hf : StrictMono f) :
    toColex (s.image f) <= toColex (t.image f) ↔ toColex s <= toColex t := by
  simp [toColex_le_toColex, hf.le_iff_le, hf.injective.eq_iff]

/--
lemma `toColex_image_lt_toColex_image` / 引理 `toColex_image_lt_toColex_image`

English:
lemma toColex_image_lt_toColex_image
  given: (hf : StrictMono f)
  proof: lt_iff_lt_of_le_iff_le toColex_image_le_toColex_image hf

中文:
引理 toColex_image_lt_toColex_image
  条件: (hf : 严格递增 f)
  证明: lt_iff_lt_of_le_iff_le toColex_image_le_toColex_image hf

Depends on / 依赖: lt_iff_lt_of_le_iff_le, toColex_image_le_toColex_image
-/
lemma toColex_image_lt_toColex_image (hf : StrictMono f) :
    toColex (s.image f) < toColex (t.image f) ↔ toColex s < toColex t :=
lt_iff_lt_of_le_iff_le toColex_image_le_toColex_image hf

/--
lemma `toColex_image_ofColex_strictMono` / 引理 `toColex_image_ofColex_strictMono`

English:
lemma toColex_image_ofColex_strictMono
  given: (hf : StrictMono f)
  proof: fun _s _t => (toColex_image_lt_toColex_image hf).2

中文:
引理 toColex_image_ofColex_strictMono
  条件: (hf : 严格递增 f)
  证明: fun _s _t => (toColex_image_lt_toColex_image hf).2

Depends on / 依赖: toColex_image_lt_toColex_image
-/
lemma toColex_image_ofColex_strictMono (hf : StrictMono f) :
StrictMono fun s => toColex image f ofColex s :=
  fun _s _t => (toColex_image_lt_toColex_image hf).2

section Fintype
variable [Fintype α]

/--
Instance `instBoundedOrder` / 实例 `instBoundedOrder`

English:
instance instBoundedOrder
  signature: : BoundedOrder (Colex (Finset α)) where
  body: toColex univ
le_top _x := toColex_le_toColex_of_subset subset_univ _

中文:
实例 instBoundedOrder
  签名: : 有界序 (Colex (有限集 α)) where
  定义体: toColex univ
le_top _x := toColex_le_toColex_of_subset subset_univ _

Depends on / 依赖: toColex
-/
instance instBoundedOrder : BoundedOrder (Colex (Finset α)) where
  top := toColex univ
le_top _x := toColex_le_toColex_of_subset subset_univ _

/--
lemma `toColex_univ` / 引理 `toColex_univ`

English:
lemma toColex_univ
  statement: toColex (univ : Finset α) = ⊤
  proof: rfl

中文:
引理 toColex_univ
  结论: toColex (univ : 有限集 α) = ⊤
  证明: rfl
-/
@[simp] lemma toColex_univ : toColex (univ : Finset α) = ⊤ := rfl
/--
lemma `ofColex_top` / 引理 `ofColex_top`

English:
lemma ofColex_top
  statement: ofColex (⊤ : Colex (Finset α)) = univ
  proof: rfl

中文:
引理 ofColex_top
  结论: ofColex (⊤ : Colex (有限集 α)) = univ
  证明: rfl
-/
@[simp] lemma ofColex_top : ofColex (⊤ : Colex (Finset α)) = univ := rfl

end Fintype

/-! ### Initial segments -/

/--
Definition of `IsInitSeg` / `IsInitSeg` 的定义

English:
definition IsInitSeg
  signature: (𝒜 : Finset (Finset α)) (r : Nat)
  body: (𝒜 : Set (Finset α)).Sized r ∧
    forall ⦃s t : Finset α⦄, s in 𝒜 -> toColex t < toColex s ∧ #t = r -> t in 𝒜

中文:
定义 IsInitSeg
  签名: (𝒜 : 有限集 (有限集 α)) (r : 自然数)
  定义体: (𝒜 : Set (Finset α)).Sized r ∧
    forall ⦃s t : Finset α⦄, s in 𝒜 -> toColex t < toColex s ∧ #t = r -> t in 𝒜

Depends on / 依赖: Finset, toColex
-/
def IsInitSeg (𝒜 : Finset (Finset α)) (r : Nat) : Prop :=
  (𝒜 : Set (Finset α)).Sized r ∧
    forall ⦃s t : Finset α⦄, s in 𝒜 -> toColex t < toColex s ∧ #t = r -> t in 𝒜

/--
lemma `isInitSeg_empty` / 引理 `isInitSeg_empty`

English:
lemma isInitSeg_empty
  statement: IsInitSeg (∅ : Finset (Finset α)) r
  proof: by simp [IsInitSeg]

中文:
引理 isInitSeg_empty
  结论: IsInitSeg (∅ : 有限集 (有限集 α)) r
  证明: by simp [IsInitSeg]
-/
@[simp] lemma isInitSeg_empty : IsInitSeg (∅ : Finset (Finset α)) r := by simp [IsInitSeg]

/--
lemma `IsInitSeg.total` / 引理 `IsInitSeg.total`

English:
lemma IsInitSeg.total
  given: (h₁ : IsInitSeg 𝒜₁ r) (h₂ : IsInitSeg 𝒜₂ r)
  statement: 𝒜₁ subseteq 𝒜₂ ∨ 𝒜₂ subseteq 𝒜₁
  proof: by
  simp_rw [← sdiff_eq_empty_iff_subset]
  by_contra! h
  have ⟨⟨s, hs⟩, t, ht⟩ := h
  rw [mem_sdiff] at hs ht
  obtain hst | hst | hts := trichotomous_of (α := Colex (Finset α)) (· < ·) (toColex s) (toColex t)
· exact hs.2 h₂.2 ht.1 ⟨hst, h₁.1 hs.1⟩
  · simp only [toColex_inj] at hst
exact ht.2 h

中文:
引理 IsInitSeg.total
  条件: (h₁ : IsInitSeg 𝒜₁ r) (h₂ : IsInitSeg 𝒜₂ r)
  结论: 𝒜₁ subseteq 𝒜₂ ∨ 𝒜₂ subseteq 𝒜₁
  证明: by
  simp_rw [← sdiff_eq_empty_iff_subset]
  by_contra! h
  have ⟨⟨s, hs⟩, t, ht⟩ := h
  rw [mem_sdiff] at hs ht
  obtain hst | hst | hts := trichotomous_of (α := Colex (Finset α)) (· < ·) (toColex s) (toColex t)
· exact hs.2 h₂.2 ht.1 ⟨hst, h₁.1 hs.1⟩
  · simp only [toColex_inj] at hst
exact ht.2 h

Depends on / 依赖: Finset, mem_sdiff, sdiff_eq_empty_iff_subset, simp_rw, toColex, toColex_inj, trichotomous_of
-/
lemma IsInitSeg.total (h₁ : IsInitSeg 𝒜₁ r) (h₂ : IsInitSeg 𝒜₂ r) : 𝒜₁ subseteq 𝒜₂ ∨ 𝒜₂ subseteq 𝒜₁ := by
  simp_rw [← sdiff_eq_empty_iff_subset]
  by_contra! h
  have ⟨⟨s, hs⟩, t, ht⟩ := h
  rw [mem_sdiff] at hs ht
  obtain hst | hst | hts := trichotomous_of (α := Colex (Finset α)) (· < ·) (toColex s) (toColex t)
· exact hs.2 h₂.2 ht.1 ⟨hst, h₁.1 hs.1⟩
  · simp only [toColex_inj] at hst
exact ht.2 hst ▸ hs.1
· exact ht.2 h₁.2 hs.1 ⟨hts, h₂.1 ht.1⟩

variable [Fintype α]

/--
Definition of `initSeg` / `initSeg` 的定义

English:
definition initSeg
  signature: (s : Finset α)
  body: {t | #s = #t ∧ toColex t <= toColex s}

@[simp]

中文:
定义 initSeg
  签名: (s : 有限集 α)
  定义体: {t | #s = #t ∧ toColex t <= toColex s}

@[simp]

Depends on / 依赖: toColex
-/
def initSeg (s : Finset α) : Finset (Finset α) := {t | #s = #t ∧ toColex t <= toColex s}

@[simp]
/--
lemma `mem_initSeg` / 引理 `mem_initSeg`

English:
lemma mem_initSeg
  statement: t in initSeg s ↔ #s = #t ∧ toColex t <= toColex s
  proof: by simp [initSeg]

中文:
引理 mem_initSeg
  结论: t in initSeg s ↔ #s = #t ∧ toColex t <= toColex s
  证明: by simp [initSeg]

Depends on / 依赖: initSeg
-/
lemma mem_initSeg : t in initSeg s ↔ #s = #t ∧ toColex t <= toColex s := by simp [initSeg]

/--
lemma `mem_initSeg_self` / 引理 `mem_initSeg_self`

English:
lemma mem_initSeg_self
  statement: s in initSeg s
  proof: by simp

中文:
引理 mem_initSeg_self
  结论: s in initSeg s
  证明: by simp

Depends on / 依赖: Nonempty, initSeg, initSeg_nonempty, mem_initSeg_self
-/
lemma mem_initSeg_self : s in initSeg s := by simp
/--
lemma `initSeg_nonempty` / 引理 `initSeg_nonempty`

English:
lemma initSeg_nonempty
  statement: (initSeg s).Nonempty
  proof: ⟨s, mem_initSeg_self⟩

中文:
引理 initSeg_nonempty
  结论: (initSeg s).非空
  证明: ⟨s, mem_initSeg_self⟩
-/
@[simp] lemma initSeg_nonempty : (initSeg s).Nonempty := ⟨s, mem_initSeg_self⟩

/--
lemma `isInitSeg_initSeg` / 引理 `isInitSeg_initSeg`

English:
lemma isInitSeg_initSeg
  statement: IsInitSeg (initSeg s) #s
  proof: by
  refine ⟨fun t ht => (mem_initSeg.1 ht).1.symm, fun t₁ t₂ ht₁ ht₂ => mem_initSeg.2 ⟨ht₂.2.symm, ?_⟩⟩
  rw [mem_initSeg] at ht₁
  exact ht₂.1.le.trans ht₁.2

中文:
引理 isInitSeg_initSeg
  结论: IsInitSeg (initSeg s) #s
  证明: by
  refine ⟨fun t ht => (mem_initSeg.1 ht).1.symm, fun t₁ t₂ ht₁ ht₂ => mem_initSeg.2 ⟨ht₂.2.symm, ?_⟩⟩
  rw [mem_initSeg] at ht₁
  exact ht₂.1.le.trans ht₁.2

Depends on / 依赖: le.trans, mem_initSeg
-/
lemma isInitSeg_initSeg : IsInitSeg (initSeg s) #s := by
  refine ⟨fun t ht => (mem_initSeg.1 ht).1.symm, fun t₁ t₂ ht₁ ht₂ => mem_initSeg.2 ⟨ht₂.2.symm, ?_⟩⟩
  rw [mem_initSeg] at ht₁
  exact ht₂.1.le.trans ht₁.2

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsInitSeg.exists_initSeg` / 引理 `IsInitSeg.exists_initSeg`

English:
lemma IsInitSeg.exists_initSeg
  given: (h𝒜 : IsInitSeg 𝒜 r) (h𝒜₀ : 𝒜.Nonempty)
  proof: by
  have hs := sup'_mem (ofColex ⁻¹' 𝒜) (LinearOrder.supClosed _) 𝒜 h𝒜₀ toColex
    (fun a ha => by simpa using ha)
  refine ⟨_, h𝒜.1 hs, ?_⟩
  ext t
  rw [mem_initSeg]
  refine ⟨fun p => ?_, ?_⟩
  · rw [h𝒜.1 p, h𝒜.1 hs]
    exact ⟨rfl, le_sup' _ p⟩
  rintro ⟨cards, le⟩
  obtain p | p := le.eq_or_l

中文:
引理 IsInitSeg.存在_initSeg
  条件: (h𝒜 : IsInitSeg 𝒜 r) (h𝒜₀ : 𝒜.非空)
  证明: by
  have hs := sup'_mem (ofColex ⁻¹' 𝒜) (LinearOrder.supClosed _) 𝒜 h𝒜₀ toColex
    (fun a ha => by simpa using ha)
  refine ⟨_, h𝒜.1 hs, ?_⟩
  ext t
  rw [mem_initSeg]
  refine ⟨fun p => ?_, ?_⟩
  · rw [h𝒜.1 p, h𝒜.1 hs]
    exact ⟨rfl, le_sup' _ p⟩
  rintro ⟨cards, le⟩
  obtain p | p := le.eq_or_l

Depends on / 依赖: LinearOrder, LinearOrder.supClosed, _mem, eq_or_lt, le.eq_or_lt, le_sup, mem_initSeg, ofColex, supClosed, toColex, toColex_inj
-/
lemma IsInitSeg.exists_initSeg (h𝒜 : IsInitSeg 𝒜 r) (h𝒜₀ : 𝒜.Nonempty) :
    exists s : Finset α, #s = r ∧ 𝒜 = initSeg s := by
  have hs := sup'_mem (ofColex ⁻¹' 𝒜) (LinearOrder.supClosed _) 𝒜 h𝒜₀ toColex
    (fun a ha => by simpa using ha)
  refine ⟨_, h𝒜.1 hs, ?_⟩
  ext t
  rw [mem_initSeg]
  refine ⟨fun p => ?_, ?_⟩
  · rw [h𝒜.1 p, h𝒜.1 hs]
    exact ⟨rfl, le_sup' _ p⟩
  rintro ⟨cards, le⟩
  obtain p | p := le.eq_or_lt
  · rwa [toColex_inj.1 p]
  · exact h𝒜.2 hs ⟨p, cards ▸ h𝒜.1 hs⟩

/--
lemma `isInitSeg_iff_exists_initSeg` / 引理 `isInitSeg_iff_exists_initSeg`

English:
lemma isInitSeg_iff_exists_initSeg
  proof: by
  refine ⟨fun h𝒜 => h𝒜.1.exists_initSeg h𝒜.2, ?_⟩
  rintro ⟨s, rfl, rfl⟩
  exact ⟨isInitSeg_initSeg, initSeg_nonempty⟩

中文:
引理 isInitSeg_iff_存在_initSeg
  证明: by
  refine ⟨fun h𝒜 => h𝒜.1.exists_initSeg h𝒜.2, ?_⟩
  rintro ⟨s, rfl, rfl⟩
  exact ⟨isInitSeg_initSeg, initSeg_nonempty⟩

Depends on / 依赖: exists_initSeg, initSeg_nonempty, isInitSeg_initSeg
-/
lemma isInitSeg_iff_exists_initSeg :
    IsInitSeg 𝒜 r ∧ 𝒜.Nonempty ↔ exists s : Finset α, #s = r ∧ 𝒜 = initSeg s := by
  refine ⟨fun h𝒜 => h𝒜.1.exists_initSeg h𝒜.2, ?_⟩
  rintro ⟨s, rfl, rfl⟩
  exact ⟨isInitSeg_initSeg, initSeg_nonempty⟩

end Colex

/-!
### Colex on `ℕ`

The colexicographic order agrees with the order induced by interpreting a set of naturals as a
`n`-ary expansion.
-/

section Nat
variable {s t : Finset Nat} {n : Nat}

/--
lemma `geomSum_ofColex_strictMono` / 引理 `geomSum_ofColex_strictMono`

English:
lemma geomSum_ofColex_strictMono
  given: (hn : 2 <= n)
  statement: StrictMono fun s => ∑ k in ofColex s, n ^ k
  proof: by
  intro s t hst
  rw [Colex.lt_iff_exists_forall_lt] at hst
  obtain ⟨a, hat, has, ha⟩ := hst
  rw [← sum_sdiff_lt_sum_sdiff]
exact (Nat.geomSum_lt hn <| by simpa).trans_le single_le_sum (fun _ _ => by lia)
    mem_sdiff.2 ⟨hat, has⟩

中文:
引理 geomSum_ofColex_strictMono
  条件: (hn : 2 <= n)
  结论: 严格递增 fun s => ∑ k in ofColex s, n ^ k
  证明: by
  intro s t hst
  rw [Colex.lt_iff_exists_forall_lt] at hst
  obtain ⟨a, hat, has, ha⟩ := hst
  rw [← sum_sdiff_lt_sum_sdiff]
exact (Nat.geomSum_lt hn <| by simpa).trans_le single_le_sum (fun _ _ => by lia)
    mem_sdiff.2 ⟨hat, has⟩

Depends on / 依赖: Colex.lt_iff_exists_forall_lt, Nat.geomSum_lt, geomSum_lt, lt_iff_exists_forall_lt, mem_sdiff, single_le_sum, sum_sdiff_lt_sum_sdiff, trans_le
-/
lemma geomSum_ofColex_strictMono (hn : 2 <= n) : StrictMono fun s => ∑ k in ofColex s, n ^ k := by
  intro s t hst
  rw [Colex.lt_iff_exists_forall_lt] at hst
  obtain ⟨a, hat, has, ha⟩ := hst
  rw [← sum_sdiff_lt_sum_sdiff]
exact (Nat.geomSum_lt hn <| by simpa).trans_le single_le_sum (fun _ _ => by lia)
    mem_sdiff.2 ⟨hat, has⟩

/--
lemma `geomSum_le_geomSum_iff_toColex_le_toColex` / 引理 `geomSum_le_geomSum_iff_toColex_le_toColex`

English:
lemma geomSum_le_geomSum_iff_toColex_le_toColex
  given: (hn : 2 <= n)
  proof: (geomSum_ofColex_strictMono hn).le_iff_le

中文:
引理 geomSum_le_geomSum_iff_toColex_le_toColex
  条件: (hn : 2 <= n)
  证明: (geomSum_ofColex_strictMono hn).le_iff_le

Depends on / 依赖: geomSum_ofColex_strictMono, le_iff_le
-/
lemma geomSum_le_geomSum_iff_toColex_le_toColex (hn : 2 <= n) :
    ∑ k in s, n ^ k <= ∑ k in t, n ^ k ↔ toColex s <= toColex t :=
  (geomSum_ofColex_strictMono hn).le_iff_le

/--
lemma `geomSum_lt_geomSum_iff_toColex_lt_toColex` / 引理 `geomSum_lt_geomSum_iff_toColex_lt_toColex`

English:
lemma geomSum_lt_geomSum_iff_toColex_lt_toColex
  given: (hn : 2 <= n)
  proof: (geomSum_ofColex_strictMono hn).lt_iff_lt

中文:
引理 geomSum_lt_geomSum_iff_toColex_lt_toColex
  条件: (hn : 2 <= n)
  证明: (geomSum_ofColex_strictMono hn).lt_iff_lt

Depends on / 依赖: geomSum_ofColex_strictMono, lt_iff_lt
-/
lemma geomSum_lt_geomSum_iff_toColex_lt_toColex (hn : 2 <= n) :
    ∑ i in s, n ^ i < ∑ i in t, n ^ i ↔ toColex s < toColex t :=
  (geomSum_ofColex_strictMono hn).lt_iff_lt

/--
theorem `geomSum_injective` / 定理 `geomSum_injective`

English:
theorem geomSum_injective
  given: {n : Nat} (hn : 2 <= n)
  proof: by
  intro _ _ h
  rwa [le_antisymm_iff, geomSum_le_geomSum_iff_toColex_le_toColex hn,
    geomSum_le_geomSum_iff_toColex_le_toColex hn, ← le_antisymm_iff] at h

中文:
定理 geomSum_injective
  条件: {n : 自然数} (hn : 2 <= n)
  证明: by
  intro _ _ h
  rwa [le_antisymm_iff, geomSum_le_geomSum_iff_toColex_le_toColex hn,
    geomSum_le_geomSum_iff_toColex_le_toColex hn, ← le_antisymm_iff] at h

Depends on / 依赖: geomSum_le_geomSum_iff_toColex_le_toColex, le_antisymm_iff
-/
theorem geomSum_injective {n : Nat} (hn : 2 <= n) :
    Function.Injective (fun s : Finset Nat => ∑ i in s, n ^ i) := by
  intro _ _ h
  rwa [le_antisymm_iff, geomSum_le_geomSum_iff_toColex_le_toColex hn,
    geomSum_le_geomSum_iff_toColex_le_toColex hn, ← le_antisymm_iff] at h

/--
theorem `lt_geomSum_of_mem` / 定理 `lt_geomSum_of_mem`

English:
theorem lt_geomSum_of_mem
  given: {a : Nat} (hn : 2 <= n) (hi : a in s)
  statement: a < ∑ i in s, n ^ i
  proof: (a.lt_pow_self hn).trans_le single_le_sum (by simp) hi

中文:
定理 lt_geomSum_of_mem
  条件: {a : 自然数} (hn : 2 <= n) (hi : a in s)
  结论: a < ∑ i in s, n ^ i
  证明: (a.lt_pow_self hn).trans_le single_le_sum (by simp) hi

Depends on / 依赖: a.lt_pow_self, lt_pow_self, single_le_sum, trans_le
-/
theorem lt_geomSum_of_mem {a : Nat} (hn : 2 <= n) (hi : a in s) : a < ∑ i in s, n ^ i :=
(a.lt_pow_self hn).trans_le single_le_sum (by simp) hi

/--
theorem `toFinset_bitIndices_sum_two_pow` / 定理 `toFinset_bitIndices_sum_two_pow`

English:
theorem toFinset_bitIndices_sum_two_pow
  given: (s : Finset Nat)
  proof: by
  simp [← (geomSum_injective rfl.le).eq_iff, List.sum_toFinset _ Nat.bitIndices_sorted.nodup]

中文:
定理 toFinset_bitIndices_sum_two_pow
  条件: (s : 有限集 自然数)
  证明: by
  simp [← (geomSum_injective rfl.le).eq_iff, List.sum_toFinset _ Nat.bitIndices_sorted.nodup]
-/
@[simp] theorem toFinset_bitIndices_sum_two_pow (s : Finset Nat) :
    (∑ i in s, 2 ^ i).bitIndices.toFinset = s := by
  simp [← (geomSum_injective rfl.le).eq_iff, List.sum_toFinset _ Nat.bitIndices_sorted.nodup]

/--
theorem `sum_toFinset_bitIndices_two_pow` / 定理 `sum_toFinset_bitIndices_two_pow`

English:
theorem sum_toFinset_bitIndices_two_pow
  given: (n : Nat)
  proof: by
  simp [List.sum_toFinset _ Nat.bitIndices_sorted.nodup]

@[deprecated (since := "2026-05-15")] alias toFinset_bitIndices_twoPowSum :=
  toFinset_bitIndices_sum_two_pow

@[deprecated (since := "2026-05-15")] alias twoPowSum_toFinset_bitIndices :=
  sum_toFinset_bitIndices_two_pow

中文:
定理 sum_toFinset_bitIndices_two_pow
  条件: (n : 自然数)
  证明: by
  simp [List.sum_toFinset _ Nat.bitIndices_sorted.nodup]

@[deprecated (since := "2026-05-15")] alias toFinset_bitIndices_twoPowSum :=
  toFinset_bitIndices_sum_two_pow

@[deprecated (since := "2026-05-15")] alias twoPowSum_toFinset_bitIndices :=
  sum_toFinset_bitIndices_two_pow
-/
@[simp] theorem sum_toFinset_bitIndices_two_pow (n : Nat) :
    ∑ i in n.bitIndices.toFinset, 2 ^ i = n := by
  simp [List.sum_toFinset _ Nat.bitIndices_sorted.nodup]

@[deprecated (since := "2026-05-15")] alias toFinset_bitIndices_twoPowSum :=
  toFinset_bitIndices_sum_two_pow

@[deprecated (since := "2026-05-15")] alias twoPowSum_toFinset_bitIndices :=
  sum_toFinset_bitIndices_two_pow

/--
Definition of `equivBitIndices` / `equivBitIndices` 的定义

English:
definition equivBitIndices
  signature: : Nat ≃ Finset Nat where
  body: n.bitIndices.toFinset
  invFun s := ∑ i in s, 2 ^ i
  left_inv := sum_toFinset_bitIndices_two_pow
  right_inv := toFinset_bitIndices_sum_two_pow

中文:
定义 equivBitIndices
  签名: : 自然数 ≃ 有限集 自然数 where
  定义体: n.bitIndices.toFinset
  invFun s := ∑ i in s, 2 ^ i
  left_inv := sum_toFinset_bitIndices_two_pow
  right_inv := toFinset_bitIndices_sum_two_pow
-/
@[simps] def equivBitIndices : Nat ≃ Finset Nat where
  toFun n := n.bitIndices.toFinset
  invFun s := ∑ i in s, 2 ^ i
  left_inv := sum_toFinset_bitIndices_two_pow
  right_inv := toFinset_bitIndices_sum_two_pow

/--
Definition of `orderIsoColex` / `orderIsoColex` 的定义

English:
definition orderIsoColex
  signature: : Nat ≃o Colex (Finset Nat) where
  body: toColex (equivBitIndices n)
  invFun s := equivBitIndices.symm (ofColex s)
  left_inv n := equivBitIndices.symm_apply_apply n
  right_inv s := equivBitIndices.apply_symm_apply _
  map_rel_iff' := by simp [← (Finset.geomSum_le_geomSum_iff_toColex_le_toColex rfl.le)]

中文:
定义 orderIsoColex
  签名: : 自然数 ≃o Colex (有限集 自然数) where
  定义体: toColex (equivBitIndices n)
  invFun s := equivBitIndices.symm (ofColex s)
  left_inv n := equivBitIndices.symm_apply_apply n
  right_inv s := equivBitIndices.apply_symm_apply _
  map_rel_iff' := by simp [← (Finset.geomSum_le_geomSum_iff_toColex_le_toColex rfl.le)]
-/
@[simps] def orderIsoColex : Nat ≃o Colex (Finset Nat) where
  toFun n := toColex (equivBitIndices n)
  invFun s := equivBitIndices.symm (ofColex s)
  left_inv n := equivBitIndices.symm_apply_apply n
  right_inv s := equivBitIndices.apply_symm_apply _
  map_rel_iff' := by simp [← (Finset.geomSum_le_geomSum_iff_toColex_le_toColex rfl.le)]

end Nat
end Finset
