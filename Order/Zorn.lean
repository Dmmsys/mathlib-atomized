/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.CompleteLattice.Chain
public import Mathlib.Order.Minimal

/-!
# Zorn's lemmas

This file proves several formulations of Zorn's Lemma.

## Variants

The primary statement of Zorn's lemma is `exists_maximal_of_chains_bounded`. Then it is specialized
to particular relations:
* `(≤)` with `zorn_le`
* `(⊆)` with `zorn_subset`
* `(⊇)` with `zorn_superset`

Lemma names carry modifiers:
* `₀`: Quantifies over a set, as opposed to over a type.
* `_nonempty`: Doesn't ask to prove that the empty chain is bounded and lets you give an element
  that will be smaller than the maximal element found (the maximal element is no smaller than any
  other element, but it can also be incomparable to some).

## How-to

This file comes across as confusing to those who haven't yet used it, so here is a detailed
walkthrough:
1. Know what relation on which type/set you're looking for. See Variants above. You can discharge
  some conditions to Zorn's lemma directly using a `_nonempty` variant.
2. Write down the definition of your type/set, put a `suffices ∃ m, ∀ a, m ≺ a → a ≺ m by ...`
  (or whatever you actually need) followed by an `apply some_version_of_zorn`.
3. Fill in the details. This is where you start talking about chains.

A typical proof using Zorn could look like this
```lean
lemma zorny_lemma : zorny_statement := by
  let s : Set α := {x | whatever x}
  suffices ∃ x ∈ s, ∀ y ∈ s, y ⊆ x → y = x by -- or with another operator xxx
    proof_post_zorn
  apply zorn_subset -- or another variant
  rintro c hcs hc
  obtain rfl | hcnemp := c.eq_empty_or_nonempty -- you might need to disjunct on c empty or not
  · exact ⟨edge_case_construction,
      proof_that_edge_case_construction_respects_whatever,
      proof_that_edge_case_construction_contains_all_stuff_in_c⟩
  · exact ⟨construction,
      proof_that_construction_respects_whatever,
      proof_that_construction_contains_all_stuff_in_c⟩
```

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/

public section

open Set

variable {α β : Type*} {r : α → α → Prop} {c : Set α}

/-- Local notation for the relation being considered. -/
local infixl:50 " ≺ " => r

/-- **Zorn's lemma**

If every chain has an upper bound, then there exists a maximal element. -/
/-
**exists_maximal_of_chains_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_maximal_of_chains_bounded (h : forall c, IsChain r c -> exists ub, 
forall a in c, a ≺ ub) (trans : forall {a b c}, a ≺ b -> b ≺ c -> a ≺ c) : exist
s m, forall a, m ≺ a -> a ≺ m
参数：h : forall c, IsChain r c -> exists ub, forall a in c, a ≺ ub；trans : forall 
{a b c}, a ≺ b -> b ≺ c -> a ≺ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `maxChain_spec`：maxChain_spec : IsMaxChain r (maxChain r)
· 使用定理 `IsChain.insert`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a : α},
   IsChain r s → (∀ b ∈ s, a ≠ b → r a b ∨ r b a) → IsChain r (insert a s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s

--- 原说明 ---
**Zorn's lemma**

If every chain has an upper bound, then there exists a maximal element.
-/
theorem exists_maximal_of_chains_bounded (h : ∀ c, IsChain r c → ∃ ub, ∀ a ∈ c, a ≺ ub)
    (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) : ∃ m, ∀ a, m ≺ a → a ≺ m :=
  have : ∃ ub, ∀ a ∈ maxChain r, a ≺ ub := h _ <| maxChain_spec.left
  let ⟨ub, (hub : ∀ a ∈ maxChain r, a ≺ ub)⟩ := this
  ⟨ub, fun a ha =>
    have : IsChain r (insert a <| maxChain r) :=
      maxChain_spec.1.insert fun b hb _ => Or.inr <| trans (hub b hb) ha
    hub a <| by
      rw [maxChain_spec.right this (subset_insert _ _)]
      exact mem_insert _ _⟩

/-- A variant of Zorn's lemma. If every nonempty chain of a nonempty type has an upper bound, then
there is a maximal element.
-/
/-
**exists_maximal_of_nonempty_chains_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_maximal_of_nonempty_chains_bounded [Nonempty α] (h : forall c, IsCh
ain r c -> c.Nonempty -> exists ub, forall a in c, a ≺ ub) (trans : forall {a b 
c}, a ≺ b -> b ≺ c -> a ≺ c) : exists m, forall a, m ≺ a -> a ≺ m
参数：h : forall c, IsChain r c -> c.Nonempty -> exists ub, forall a in c, a ≺ ub；t
rans : forall {a b c}, a ≺ b -> b ≺ c -> a ≺ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_maximal_of_chains_bounded`：exists_maximal_of_chains_bounded (h : 
forall c, IsChain r c -> exists ub, forall a in c, a ≺ ub) (trans : forall {a b 
c}, a ≺ b -> b ≺ c -> …
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty

--- 原说明 ---
A variant of Zorn's lemma. If every nonempty chain of a nonempty type has an upp
er bound, then
there is a maximal element.
-/
theorem exists_maximal_of_nonempty_chains_bounded [Nonempty α]
    (h : ∀ c, IsChain r c → c.Nonempty → ∃ ub, ∀ a ∈ c, a ≺ ub)
    (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) : ∃ m, ∀ a, m ≺ a → a ≺ m :=
  exists_maximal_of_chains_bounded
    (fun c hc =>
      (eq_empty_or_nonempty c).elim
        (fun h => ⟨Classical.arbitrary α, fun x hx => (h ▸ hx : x ∈ (∅ : Set α)).elim⟩) (h c hc))
    trans

section Preorder

variable [Preorder α]

/-
**zorn_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zorn_le (h : forall c : Set α, IsChain (· <= ·) c -> BddAbove c) : exists 
m : α, IsMax m
参数：h : forall c : Set α, IsChain (· <= ·) c -> BddAbove c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_maximal_of_chains_bounded`：exists_maximal_of_chains_bounded (h : 
forall c, IsChain r c -> exists ub, forall a in c, a ≺ ub) (trans : forall {a b 
c}, a ≺ b -> b ≺ c -> …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem zorn_le (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) : ∃ m : α, IsMax m :=
  exists_maximal_of_chains_bounded h le_trans
/-
**zorn_le_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zorn_le_nonempty [Nonempty α] (h : forall c : Set α, IsChain (· <= ·) c ->
 c.Nonempty -> BddAbove c) : exists m : α, IsMax m
参数：h : forall c : Set α, IsChain (· <= ·) c -> c.Nonempty -> BddAbove c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_maximal_of_nonempty_chains_bounded`：exists_maximal_of_nonempty_ch
ains_bounded [Nonempty α] (h : forall c, IsChain r c -> c.Nonempty -> exists ub,
 forall a in c, a ≺ ub) (trans …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem zorn_le_nonempty [Nonempty α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → c.Nonempty → BddAbove c) : ∃ m : α, IsMax m :=
  exists_maximal_of_nonempty_chains_bounded h le_trans
/-
**zorn_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zorn_le (h : forall c : Set α, IsChain (· <= ·) c -> BddAbove c) : exists 
m : α, IsMax m
参数：h : forall c : Set α, IsChain (· <= ·) c -> BddAbove c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_maximal_of_chains_bounded`：exists_maximal_of_chains_bounded (h : 
forall c, IsChain r c -> exists ub, forall a in c, a ≺ ub) (trans : forall {a b 
c}, a ≺ b -> b ≺ c -> …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem zorn_le₀ (s : Set α) (ih : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) :
    ∃ m, Maximal (· ∈ s) m :=
  let ⟨⟨m, hms⟩, h⟩ :=
    @zorn_le s _ fun c hc =>
      let ⟨ub, hubs, hub⟩ :=
        ih (Subtype.val '' c) (fun _ ⟨⟨_, hx⟩, _, h⟩ => h ▸ hx)
          (by
            rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq
            exact hc hpc hqc fun t => hpq (Subtype.ext_iff.1 t))
      ⟨⟨ub, hubs⟩, fun ⟨_, _⟩ hc => hub _ ⟨_, hc, rfl⟩⟩
  ⟨m, hms, fun z hzs hmz => @h ⟨z, hzs⟩ hmz⟩
/-
**zorn_le_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zorn_le_nonempty [Nonempty α] (h : forall c : Set α, IsChain (· <= ·) c ->
 c.Nonempty -> BddAbove c) : exists m : α, IsMax m
参数：h : forall c : Set α, IsChain (· <= ·) c -> c.Nonempty -> BddAbove c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_maximal_of_nonempty_chains_bounded`：exists_maximal_of_nonempty_ch
ains_bounded [Nonempty α] (h : forall c, IsChain r c -> c.Nonempty -> exists ub,
 forall a in c, a ≺ ub) (trans …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem zorn_le_nonempty₀ (s : Set α)
    (ih : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) (x : α) (hxs : x ∈ s) :
    ∃ m, x ≤ m ∧ Maximal (· ∈ s) m := by
  have H := zorn_le₀ ({ y ∈ s | x ≤ y }) fun c hcs hc => ?_
  · rcases H with ⟨m, ⟨hms, hxm⟩, hm⟩
    exact ⟨m, hxm, hms, fun z hzs hmz => @hm _ ⟨hzs, hxm.trans hmz⟩ hmz⟩
  · rcases c.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
    · exact ⟨x, ⟨hxs, le_rfl⟩, fun z => False.elim⟩
    · rcases ih c (fun z hz => (hcs hz).1) hc y hy with ⟨z, hzs, hz⟩
      exact ⟨z, ⟨hzs, (hcs hy).2.trans <| hz _ hy⟩, hz⟩
/-
**zorn_le_nonempty_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zorn_le_nonempty_Ici₀ (a : α)
    (ih : ∀ c ⊆ Ici a, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub, ∀ z ∈ c, z ≤ ub) (x : α) (hax : a ≤ x) :
    ∃ m, x ≤ m ∧ IsMax m := by
  let ⟨m, hxm, ham, hm⟩ := zorn_le_nonempty₀ (Ici a) (fun c hca hc y hy ↦ ?_) x hax
  · exact ⟨m, hxm, fun z hmz => hm (ham.trans hmz) hmz⟩
  · have ⟨ub, hub⟩ := ih c hca hc y hy
    exact ⟨ub, (hca hy).trans (hub y hy), hub⟩

end Preorder

/-
**zorn_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zorn_subset (S : Set (Set α)) (h : forall c subseteq S, IsChain (· subsete
q ·) c -> exists ub in S, forall s in c, s subseteq ub) : exists m, Maximal (· i
n S) m
参数：S : Set (Set α)；h : forall c subseteq S, IsChain (· subseteq ·) c -> exists u
b in S, forall s in c, s subseteq ub。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_le₀`：zorn_le₀ (s : Set α) (ih : forall c subseteq s, IsChain (· <= 
·) c -> exists ub in s, forall z in c, z <= ub) : exists m, Maximal (· in s) m
-/
theorem zorn_subset (S : Set (Set α))
    (h : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) : ∃ m, Maximal (· ∈ S) m :=
  zorn_le₀ S h
/-
**zorn_subset_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zorn_subset_nonempty (S : Set (Set α)) (H : forall c subseteq S, IsChain (
· subseteq ·) c -> c.Nonempty -> exists ub in S, forall s in c, s subseteq ub) (
x) (hx : x in S) : exists m, x subseteq m ∧ Maximal (· in S) m
参数：S : Set (Set α)；H : forall c subseteq S, IsChain (· subseteq ·) c -> c.Nonemp
ty -> exists ub in S, forall s in c, s subseteq ub；x；hx : x in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_le_nonempty₀`：zorn_le_nonempty₀ (s : Set α) (ih : forall c subseteq
 s, IsChain (· <= ·) c -> forall y in c, exists ub in s, forall z in c, z <= ub)
 (x : α…
-/
theorem zorn_subset_nonempty (S : Set (Set α))
    (H : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) (x) (hx : x ∈ S) :
    ∃ m, x ⊆ m ∧ Maximal (· ∈ S) m :=
  zorn_le_nonempty₀ _ (fun _ cS hc y yc => H _ cS hc ⟨y, yc⟩) _ hx
/-
**zorn_superset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zorn_superset (S : Set (Set α)) (h : forall c subseteq S, IsChain (· subse
teq ·) c -> exists lb in S, forall s in c, lb subseteq s) : exists m, Minimal (·
 in S) m
参数：S : Set (Set α)；h : forall c subseteq S, IsChain (· subseteq ·) c -> exists l
b in S, forall s in c, lb subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_le₀`：zorn_le₀ (s : Set α) (ih : forall c subseteq s, IsChain (· <= 
·) c -> exists ub in s, forall z in c, z <= ub) : exists m, Maximal (· in s) m
· 使用定理 `IsChain.symm`：IsChain.symm (h : IsChain r s) : IsChain (flip r) s
-/
theorem zorn_superset (S : Set (Set α))
    (h : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) : ∃ m, Minimal (· ∈ S) m :=
  (@zorn_le₀ (Set α)ᵒᵈ _ S) fun c cS hc => h c cS hc.symm
/-
**zorn_superset_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zorn_superset_nonempty (S : Set (Set α)) (H : forall c subseteq S, IsChain
 (· subseteq ·) c -> c.Nonempty -> exists lb in S, forall s in c, lb subseteq s)
 (x) (hx : x in S) : exists m, m subseteq x ∧ Minimal (· in S) m
参数：S : Set (Set α)；H : forall c subseteq S, IsChain (· subseteq ·) c -> c.Nonemp
ty -> exists lb in S, forall s in c, lb subseteq s；x；hx : x in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_le_nonempty₀`：zorn_le_nonempty₀ (s : Set α) (ih : forall c subseteq
 s, IsChain (· <= ·) c -> forall y in c, exists ub in s, forall z in c, z <= ub)
 (x : α…
· 使用定理 `IsChain.symm`：IsChain.symm (h : IsChain r s) : IsChain (flip r) s
-/
theorem zorn_superset_nonempty (S : Set (Set α))
    (H : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) (x) (hx : x ∈ S) :
    ∃ m, m ⊆ x ∧ Minimal (· ∈ S) m :=
  @zorn_le_nonempty₀ (Set α)ᵒᵈ _ S (fun _ cS hc y yc => H _ cS hc.symm ⟨y, yc⟩) _ hx

/-- Every chain is contained in a maximal chain. This generalizes Hausdorff's maximality principle.
-/
/-
**IsChain.exists_maxChain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.exists_maxChain (hc : IsChain r c) : exists M, @IsMaxChain _ r M ∧
 c subseteq M
参数：hc : IsChain r c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_subset_nonempty`：zorn_subset_nonempty (S : Set (Set α)) (H : forall
 c subseteq S, IsChain (· subseteq ·) c -> c.Nonempty -> exists ub in S, forall 
s in c, s …
· 使用定理 `Set.mem_sUnion_of_mem`：mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (S
et α)} (hx : x in t) (ht : t in S) : x in ⋃₀ S
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `Maximal.eq_of_subset`：Maximal.eq_of_subset (h : Maximal P s) (ht : P t) 
(hst : s subseteq t) : s = t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
Every chain is contained in a maximal chain. This generalizes Hausdorff's maxima
lity principle.
-/
theorem IsChain.exists_maxChain (hc : IsChain r c) : ∃ M, @IsMaxChain _ r M ∧ c ⊆ M := by
  have H := zorn_subset_nonempty { s | c ⊆ s ∧ IsChain r s } ?_ c ⟨Subset.rfl, hc⟩
  · obtain ⟨M, hcM, hM⟩ := H
    exact ⟨M, ⟨hM.prop.2, fun d hd hMd ↦ hM.eq_of_subset ⟨hcM.trans hMd, hd⟩ hMd⟩, hcM⟩
  rintro cs hcs₀ hcs₁ ⟨s, hs⟩
  refine
    ⟨⋃₀cs, ⟨fun _ ha => Set.mem_sUnion_of_mem ((hcs₀ hs).left ha) hs, ?_⟩, fun _ =>
      Set.subset_sUnion_of_mem⟩
  rintro y ⟨sy, hsy, hysy⟩ z ⟨sz, hsz, hzsz⟩ hyz
  obtain rfl | hsseq := eq_or_ne sy sz
  · exact (hcs₀ hsy).right hysy hzsz hyz
  rcases hcs₁ hsy hsz hsseq with h | h
  · exact (hcs₀ hsz).right (h hysy) hzsz hyz
  · exact (hcs₀ hsy).right hysy (h hzsz) hyz

/-! ### Flags -/

namespace Flag

variable [Preorder α] {c : Set α} {s : Flag α} {a b : α}

/-
**Flag._root_.IsChain.exists_subset_flag** 是 Mathlib 中的一个引理，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsChain.exists_subset_flag (hc : IsChain (· ≤ ·) c) : ∃ s : Flag α, c ⊆ s :=
  let ⟨s, hs, hcs⟩ := hc.exists_maxChain; ⟨ofIsMaxChain s hs, hcs⟩
/-
**Flag.exists_mem** 是 Mathlib 中的一个引理，位于命名空间 `Flag`。
形式化陈述：exists_mem (a : α) : exists s : Flag α, a in s
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.exists_subset_flag`：∀ {α : Type u_1} [inst : Preorder α] {c : Se
t α}, IsChain (fun x1 x2 => x1 ≤ x2) c → ∃ s, c ⊆ ↑s
· 使用定理 `Set.Subsingleton.isChain`：Set.Subsingleton.isChain (hs : s.Subsingleton)
 : IsChain r s
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
lemma exists_mem (a : α) : ∃ s : Flag α, a ∈ s :=
  let ⟨s, hs⟩ := Set.subsingleton_singleton (a := a).isChain.exists_subset_flag
  ⟨s, hs rfl⟩
/-
**Flag.exists_mem_mem** 是 Mathlib 中的一个引理，位于命名空间 `Flag`。
形式化陈述：exists_mem_mem (hab : a <= b) : exists s : Flag α, a in s ∧ b in s
参数：hab : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsChain.exists_subset_flag`：∀ {α : Type u_1} [inst : Preorder α] {c : Se
t α}, IsChain (fun x1 x2 => x1 ≤ x2) c → ∃ s, c ⊆ ↑s
· 使用引理 `IsChain.pair`：IsChain.pair (h : r a b) : IsChain r {a, b}
-/
lemma exists_mem_mem (hab : a ≤ b) : ∃ s : Flag α, a ∈ s ∧ b ∈ s := by
  simpa [Set.insert_subset_iff] using (IsChain.pair hab).exists_subset_flag
/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (Flag α) := ⟨.ofIsMaxChain _ maxChain_spec⟩

end Flag

