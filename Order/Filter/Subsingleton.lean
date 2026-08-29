/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.Order.Filter.Prod
public import Mathlib.Order.Filter.Ultrafilter.Defs
/-!
# Subsingleton filters

We say that a filter `l` is a *subsingleton* if there exists a subsingleton set `s ∈ l`.
Equivalently, `l` is either `⊥` or `pure a` for some `a`.
-/

@[expose] public section

open Set
variable {α β : Type*} {l : Filter α}

namespace Filter

/--
Definition of `Subsingleton` / `Subsingleton` 的定义

English:
definition Subsingleton
  signature: (l : Filter α)
  body: exists s in l, Set.Subsingleton s

中文:
定义 子单例
  签名: (l : 滤子 α)
  定义体: exists s in l, Set.Subsingleton s
-/
protected def Subsingleton (l : Filter α) : Prop := exists s in l, Set.Subsingleton s

/--
theorem `HasBasis.subsingleton_iff` / 定理 `HasBasis.subsingleton_iff`

English:
theorem HasBasis.subsingleton_iff
  given: {ι : Sort*} {p : ι -> Prop} {s : ι -> Set α} (h : l.HasBasis p s)
  proof: h.exists_iff fun _ _ hsub h => h.anti hsub

中文:
定理 有基.subsingleton_iff
  条件: {ι : 类型层*} {p : ι -> 命题} {s : ι -> 集合 α} (h : l.有基 p s)
  证明: h.exists_iff fun _ _ hsub h => h.anti hsub

Depends on / 依赖: exists_iff, h.anti, h.exists_iff
-/
theorem HasBasis.subsingleton_iff {ι : Sort*} {p : ι -> Prop} {s : ι -> Set α} (h : l.HasBasis p s) :
    l.Subsingleton ↔ exists i, p i ∧ (s i).Subsingleton :=
  h.exists_iff fun _ _ hsub h => h.anti hsub

/--
theorem `Subsingleton.anti` / 定理 `Subsingleton.anti`

English:
theorem Subsingleton.anti
  given: {l'} (hl : l.Subsingleton) (hl' : l' <= l)
  statement: l'.Subsingleton
  proof: let ⟨s, hsl, hs⟩ := hl; ⟨s, hl' hsl, hs⟩

@[nontriviality]

中文:
定理 子单例.anti
  条件: {l'} (hl : l.子单例) (hl' : l' <= l)
  结论: l'.子单例
  证明: let ⟨s, hsl, hs⟩ := hl; ⟨s, hl' hsl, hs⟩

@[nontriviality]
-/
theorem Subsingleton.anti {l'} (hl : l.Subsingleton) (hl' : l' <= l) : l'.Subsingleton :=
  let ⟨s, hsl, hs⟩ := hl; ⟨s, hl' hsl, hs⟩

@[nontriviality]
/--
theorem `Subsingleton.of_subsingleton` / 定理 `Subsingleton.of_subsingleton`

English:
theorem Subsingleton.of_subsingleton
  given: [Subsingleton α]
  statement: l.Subsingleton
  proof: ⟨univ, univ_mem, subsingleton_univ⟩

中文:
定理 子单例.of_subsingleton
  条件: [子单例 α]
  结论: l.子单例
  证明: ⟨univ, univ_mem, subsingleton_univ⟩

Depends on / 依赖: subsingleton_univ, univ_mem
-/
theorem Subsingleton.of_subsingleton [Subsingleton α] : l.Subsingleton :=
  ⟨univ, univ_mem, subsingleton_univ⟩

/--
theorem `Subsingleton.map` / 定理 `Subsingleton.map`

English:
theorem Subsingleton.map
  given: (hl : l.Subsingleton) (f : α -> β)
  statement: (map f l).Subsingleton
  proof: let ⟨s, hsl, hs⟩ := hl; ⟨f '' s, image_mem_map hsl, hs.image f⟩

中文:
定理 子单例.map
  条件: (hl : l.子单例) (f : α -> β)
  结论: (map f l).子单例
  证明: let ⟨s, hsl, hs⟩ := hl; ⟨f '' s, image_mem_map hsl, hs.image f⟩

Depends on / 依赖: hs.image, image_mem_map
-/
theorem Subsingleton.map (hl : l.Subsingleton) (f : α -> β) : (map f l).Subsingleton :=
  let ⟨s, hsl, hs⟩ := hl; ⟨f '' s, image_mem_map hsl, hs.image f⟩

/--
theorem `Subsingleton.prod` / 定理 `Subsingleton.prod`

English:
theorem Subsingleton.prod
  given: (hl : l.Subsingleton) {l' : Filter β} (hl' : l'.Subsingleton)
  proof: let ⟨s, hsl, hs⟩ := hl; let ⟨t, htl', ht⟩ := hl'; ⟨s ×ˢ t, prod_mem_prod hsl htl', hs.prod ht⟩

@[simp]

中文:
定理 子单例.乘积
  条件: (hl : l.子单例) {l' : 滤子 β} (hl' : l'.子单例)
  证明: let ⟨s, hsl, hs⟩ := hl; let ⟨t, htl', ht⟩ := hl'; ⟨s ×ˢ t, prod_mem_prod hsl htl', hs.prod ht⟩

@[simp]
-/
theorem Subsingleton.prod (hl : l.Subsingleton) {l' : Filter β} (hl' : l'.Subsingleton) :
    (l ×ˢ l').Subsingleton :=
  let ⟨s, hsl, hs⟩ := hl; let ⟨t, htl', ht⟩ := hl'; ⟨s ×ˢ t, prod_mem_prod hsl htl', hs.prod ht⟩

@[simp]
/--
theorem `subsingleton_pure` / 定理 `subsingleton_pure`

English:
theorem subsingleton_pure
  given: {a : α}
  statement: Filter.Subsingleton (pure a)
  proof: ⟨{a}, rfl, subsingleton_singleton⟩

@[simp]

中文:
定理 subsingleton_pure
  条件: {a : α}
  结论: 滤子.子单例 (pure a)
  证明: ⟨{a}, rfl, subsingleton_singleton⟩

@[simp]

Depends on / 依赖: subsingleton_singleton
-/
theorem subsingleton_pure {a : α} : Filter.Subsingleton (pure a) :=
  ⟨{a}, rfl, subsingleton_singleton⟩

@[simp]
/--
theorem `subsingleton_bot` / 定理 `subsingleton_bot`

English:
theorem subsingleton_bot
  statement: Filter.Subsingleton (⊥ : Filter α)
  proof: ⟨∅, trivial, subsingleton_empty⟩

中文:
定理 subsingleton_bot
  结论: 滤子.子单例 (⊥ : 滤子 α)
  证明: ⟨∅, trivial, subsingleton_empty⟩

Depends on / 依赖: subsingleton_empty
-/
theorem subsingleton_bot : Filter.Subsingleton (⊥ : Filter α) :=
  ⟨∅, trivial, subsingleton_empty⟩

/--
theorem `Subsingleton.exists_eq_pure` / 定理 `Subsingleton.exists_eq_pure`

English:
theorem Subsingleton.exists_eq_pure
  given: [l.NeBot] (hl : l.Subsingleton)
  statement: exists a, l = pure a
  proof: by
  rcases hl with ⟨s, hsl, hs⟩
  rcases exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨nonempty_of_mem hsl, hs⟩ with ⟨a, rfl⟩
  refine ⟨a, (NeBot.le_pure_iff ‹_›).1 ?_⟩
  rwa [le_pure_iff]

中文:
定理 子单例.存在_eq_pure
  条件: [l.NeBot] (hl : l.子单例)
  结论: 存在 a, l = pure a
  证明: by
  rcases hl with ⟨s, hsl, hs⟩
  rcases exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨nonempty_of_mem hsl, hs⟩ with ⟨a, rfl⟩
  refine ⟨a, (NeBot.le_pure_iff ‹_›).1 ?_⟩
  rwa [le_pure_iff]

Depends on / 依赖: NeBot.le_pure_iff, exists_eq_singleton_iff_nonempty_subsingleton, le_pure_iff, nonempty_of_mem
-/
theorem Subsingleton.exists_eq_pure [l.NeBot] (hl : l.Subsingleton) : exists a, l = pure a := by
  rcases hl with ⟨s, hsl, hs⟩
  rcases exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨nonempty_of_mem hsl, hs⟩ with ⟨a, rfl⟩
  refine ⟨a, (NeBot.le_pure_iff ‹_›).1 ?_⟩
  rwa [le_pure_iff]

/--
theorem `subsingleton_iff_bot_or_pure` / 定理 `subsingleton_iff_bot_or_pure`

English:
theorem subsingleton_iff_bot_or_pure
  statement: l.Subsingleton ↔ l = ⊥ ∨ exists a, l = pure a
  proof: by
  refine ⟨fun hl => ?_, ?_⟩
  · exact (eq_or_neBot l).imp_right (@Subsingleton.exists_eq_pure _ _ · hl)
  · rintro (rfl | ⟨a, rfl⟩) <;> simp

中文:
定理 subsingleton_iff_bot_or_pure
  结论: l.子单例 ↔ l = ⊥ ∨ 存在 a, l = pure a
  证明: by
  refine ⟨fun hl => ?_, ?_⟩
  · exact (eq_or_neBot l).imp_right (@Subsingleton.exists_eq_pure _ _ · hl)
  · rintro (rfl | ⟨a, rfl⟩) <;> simp

Depends on / 依赖: Subsingleton, Subsingleton.exists_eq_pure, eq_or_neBot, exists_eq_pure, imp_right
-/
theorem subsingleton_iff_bot_or_pure : l.Subsingleton ↔ l = ⊥ ∨ exists a, l = pure a := by
  refine ⟨fun hl => ?_, ?_⟩
  · exact (eq_or_neBot l).imp_right (@Subsingleton.exists_eq_pure _ _ · hl)
  · rintro (rfl | ⟨a, rfl⟩) <;> simp

/--
theorem `subsingleton_iff_exists_le_pure` / 定理 `subsingleton_iff_exists_le_pure`

English:
theorem subsingleton_iff_exists_le_pure
  given: [Nonempty α]
  statement: l.Subsingleton ↔ exists a, l <= pure a
  proof: by
  rcases eq_or_neBot l with rfl | hbot
  · simp
  · simp [subsingleton_iff_bot_or_pure, ← hbot.le_pure_iff, hbot.ne]

中文:
定理 subsingleton_iff_存在_le_pure
  条件: [非空 α]
  结论: l.子单例 ↔ 存在 a, l <= pure a
  证明: by
  rcases eq_or_neBot l with rfl | hbot
  · simp
  · simp [subsingleton_iff_bot_or_pure, ← hbot.le_pure_iff, hbot.ne]

Depends on / 依赖: eq_or_neBot, hbot.le_pure_iff, hbot.ne, le_pure_iff, subsingleton_iff_bot_or_pure
-/
theorem subsingleton_iff_exists_le_pure [Nonempty α] : l.Subsingleton ↔ exists a, l <= pure a := by
  rcases eq_or_neBot l with rfl | hbot
  · simp
  · simp [subsingleton_iff_bot_or_pure, ← hbot.le_pure_iff, hbot.ne]

/--
theorem `subsingleton_iff_exists_singleton_mem` / 定理 `subsingleton_iff_exists_singleton_mem`

English:
theorem subsingleton_iff_exists_singleton_mem
  given: [Nonempty α]
  statement: l.Subsingleton ↔ exists a, {a} in l
  proof: by
  simp only [subsingleton_iff_exists_le_pure, le_pure_iff]

中文:
定理 subsingleton_iff_存在_singleton_mem
  条件: [非空 α]
  结论: l.子单例 ↔ 存在 a, {a} in l
  证明: by
  simp only [subsingleton_iff_exists_le_pure, le_pure_iff]

Depends on / 依赖: le_pure_iff, subsingleton_iff_exists_le_pure
-/
theorem subsingleton_iff_exists_singleton_mem [Nonempty α] : l.Subsingleton ↔ exists a, {a} in l := by
  simp only [subsingleton_iff_exists_le_pure, le_pure_iff]

/-- A subsingleton filter on a nonempty type is less than or equal to `pure a` for some `a`. -/
alias ⟨Subsingleton.exists_le_pure, _⟩ := subsingleton_iff_exists_le_pure

/--
lemma `Subsingleton.isCountablyGenerated` / 引理 `Subsingleton.isCountablyGenerated`

English:
lemma Subsingleton.isCountablyGenerated
  given: (hl : l.Subsingleton)
  statement: IsCountablyGenerated l
  proof: by
  rcases subsingleton_iff_bot_or_pure.1 hl with rfl | ⟨x, rfl⟩
  · exact isCountablyGenerated_bot
  · exact isCountablyGenerated_pure x

中文:
引理 子单例.isCountablyGenerated
  条件: (hl : l.子单例)
  结论: 是余untablyGenerated l
  证明: by
  rcases subsingleton_iff_bot_or_pure.1 hl with rfl | ⟨x, rfl⟩
  · exact isCountablyGenerated_bot
  · exact isCountablyGenerated_pure x

Depends on / 依赖: isCountablyGenerated_bot, isCountablyGenerated_pure, subsingleton_iff_bot_or_pure
-/
lemma Subsingleton.isCountablyGenerated (hl : l.Subsingleton) : IsCountablyGenerated l := by
  rcases subsingleton_iff_bot_or_pure.1 hl with rfl | ⟨x, rfl⟩
  · exact isCountablyGenerated_bot
  · exact isCountablyGenerated_pure x

end Filter
