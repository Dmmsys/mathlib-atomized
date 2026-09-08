/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-! # Possible cycle types of permutations

* For `m : Multiset ℕ`, `Equiv.Perm.exists_with_cycleType_iff m`
  proves that there are permutations with cycleType `m` if and only if
  its sum is at most `Fintype.card α` and its members are at least 2.

-/

public section

variable (α : Type*) [DecidableEq α] [Fintype α]

section Ranges

/-- For any `c : List ℕ` whose sum is at most `Fintype.card α`,
  we can find `o : List (List α)` whose members have no duplicate,
  whose lengths given by `c`, and which are pairwise disjoint -/
/-
**List.exists_pw_disjoint_with_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.exists_pw_disjoint_with_card {α : Type*} [Fintype α] {c : List Nat} (
hc : c.sum <= Fintype.card α) : exists o : List (List α), o.map length = c ∧ (fo
rall s in o, s.Nodup) ∧ Pairwise List.Disjoint o
参数：hc : c.sum <= Fintype.card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `List.mem_mem_ranges_iff_lt_sum`：mem_mem_ranges_iff_lt_sum (l : List Nat)
 {n : Nat} : (exists s in l.ranges, n in s) ↔ n < l.sum
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_id`：∀ {α : Type u_1} (l : List α), List.map id l = l
· 使用定理 `List.map_pmap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {p : α → P
rop} {g : β → γ} {f : (a : α) → p a → β} {l : List α}   (H : ∀ a ∈ l, p a), List
.ma…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.pmap.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {P : α → Prop} (f 
f_1 : (a : α) → P a → β),   f = f_1 → ∀ (l l_1 : List α) (e_l : l = l_1) (H : ∀ 
a ∈ l, P a…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.valEmbedding_apply`：∀ {n : ℕ}, ⇑Fin.valEmbedding = Fin.val
· 使用定理 `List.pmap_eq_map`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : α 
→ β} {l : List α} (H : ∀ a ∈ l, p a),   List.pmap (fun a x => f a) l H = List.ma
p f l
· 使用定理 `List.map_id'`：∀ {α : Type u_1} (l : List α), List.map (fun a => a) l = l
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `List.ranges_length`：ranges_length (l : List Nat) : l.ranges.map length =
 l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a
 : α) → p a → β} {l : List α} {H : ∀ a ∈ l, p a},   (List.pmap f l H).length = l
.lengt…
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `List.Nodup.map`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β}, Fu
nction.Injective f → l.Nodup → (List.map f l).Nodup
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a : 
α) → p a → β} {l : List α} {H : ∀ a ∈ l, p a} {b : β},   b ∈ List.pmap f l H ↔ ∃
 a,…
· 使用定理 `List.Nodup.of_map`：∀ {α : Type u} {β : Type v} (f : α → β) {l : List α},
 (List.map f l).Nodup → l.Nodup
· 使用定理 `List.ranges_nodup`：ranges_nodup {l s : List Nat} (hs : s in ranges l) : 
s.Nodup
· 使用定理 `List.Pairwise.map`：∀ {β : Type u_1} {α : Type u_2} {R : α → α → Prop} {l
 : List α} {S : β → β → Prop} (f : α → β),   (∀ (a b : α), R a b → S (f a) (f b)
) → Lis…
· 使用定理 `List.disjoint_map`：disjoint_map {f : α -> β} {s t : List α} (hf : Functi
on.Injective f) (h : Disjoint s t) : Disjoint (s.map f) (t.map f)
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
For any `c : List ℕ` whose sum is at most `Fintype.card α`,
  we can find `o : List (List α)` whose members have no duplicate,
  whose lengths given by `c`, and which are pairwise disjoint
-/
theorem List.exists_pw_disjoint_with_card {α : Type*} [Fintype α]
    {c : List ℕ} (hc : c.sum ≤ Fintype.card α) :
    ∃ o : List (List α),
      o.map length = c ∧ (∀ s ∈ o, s.Nodup) ∧ Pairwise List.Disjoint o := by
  let klift (n : ℕ) (hn : n < Fintype.card α) : Fin (Fintype.card α) :=
    (⟨n, hn⟩ : Fin (Fintype.card α))
  let klift' (l : List ℕ) (hl : ∀ a ∈ l, a < Fintype.card α) :
    List (Fin (Fintype.card α)) := List.pmap klift l hl
  have hc'_lt : ∀ l ∈ c.ranges, ∀ n ∈ l, n < Fintype.card α := by
    intro l hl n hn
    apply lt_of_lt_of_le _ hc
    rw [← mem_mem_ranges_iff_lt_sum]
    exact ⟨l, hl, hn⟩
  let l := (ranges c).pmap klift' hc'_lt
  have hl : ∀ (a : List ℕ) (ha : a ∈ c.ranges),
    (klift' a (hc'_lt a ha)).map Fin.valEmbedding = a := by
    intro a ha
    conv_rhs => rw [← List.map_id a]
    rw [List.map_pmap]
    simp [klift, Fin.valEmbedding_apply, List.pmap_eq_map, List.map_id']
  use l.map (List.map (Fintype.equivFin α).symm)
  constructor
  · -- length
    rw [← ranges_length c]
    simp only [l, klift', map_pmap, length_pmap,
      pmap_eq_map]
  constructor
  · -- nodup
    intro s
    rw [mem_map]
    rintro ⟨t, ht, rfl⟩
    apply Nodup.map (Equiv.injective _)
    obtain ⟨u, hu, rfl⟩ := mem_pmap.mp ht
    apply Nodup.of_map
    rw [hl u hu]
    exact ranges_nodup hu
  · -- pairwise disjoint
    refine Pairwise.map _ (fun s t ↦ disjoint_map (Equiv.injective _)) ?_
    -- List.Pairwise List.disjoint l
    apply Pairwise.pmap (List.ranges_disjoint c)
    intro u hu v hv huv
    apply disjoint_pmap
    · intro a a' ha ha' h
      simpa only [klift, Fin.mk_eq_mk] using h
    exact huv

end Ranges

/-- There are permutations with cycleType `m` if and only if
  its sum is at most `Fintype.card α` and its members are at least 2. -/
/-
**Equiv.Perm.exists_with_cycleType_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.exists_with_cycleType_iff {m : Multiset Nat} : (exists g : Equi
v.Perm α, g.cycleType = m) ↔ (m.sum <= Fintype.card α ∧ forall a in m, 2 <= a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.sum_cycleType`：sum_cycleType (σ : Perm α) : σ.cycleType.sum =
 #σ.support
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `Equiv.Perm.two_le_of_mem_cycleType`：two_le_of_mem_cycleType {σ : Perm α}
 {n : Nat} (h : n in σ.cycleType) : 2 <= n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.sum_toList`：∀ {M : Type u_3} [inst : AddCommMonoid M] (s : Mult
iset M), s.toList.sum = s.sum
· 使用定理 `List.exists_pw_disjoint_with_card`：List.exists_pw_disjoint_with_card {α 
: Type*} [Fintype α] {c : List Nat} (hc : c.sum <= Fintype.card α) : exists o : 
List (List α), o.map le…
· 使用定理 `Multiset.mem_toList`：mem_toList {a : α} {s : Multiset α} : a in s.toList
 ↔ a in s
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Equiv.Perm.cycleType_eq`：cycleType_eq {σ : Perm α} (l : List (Perm α)) (
h0 : l.prod = σ) (h1 : forall σ : Perm α, σ in l -> σ.IsCycle) (h2 : l.Pairwise 
Disjoint) : σ…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.isCycle_formPerm`：isCycle_formPerm (hl : Nodup l) (hn : 2 <= l.leng
th) : IsCycle (formPerm l)
· 使用定理 `List.pairwise_map`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1} {R : 
α_1 → α_1 → Prop} {l : List α},   List.Pairwise R (List.map f l) ↔ List.Pairwise
 (fun a…
· 使用定理 `List.Pairwise.imp_of_mem`：∀ {α : Type u_1} {l : List α} {R S : α → α → P
rop},   (∀ {a b : α}, a ∈ l → b ∈ l → R a b → S a b) → List.Pairwise R l → List.
Pairwise S l
· 使用定理 `List.formPerm_disjoint_iff`：formPerm_disjoint_iff (hl : Nodup l) (hl' : 
Nodup l') (hn : 2 <= l.length) (hn' : 2 <= l'.length) : Perm.Disjoint (formPerm 
l) (formPerm l')…
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.map_congr_left`：∀ {α : Type u_1} {l : List α} {α_1 : Type u_2} {f g
 : α → α_1}, (∀ a ∈ l, f a = g a) → List.map f l = List.map g l
· 使用定理 `List.support_formPerm_of_nodup`：support_formPerm_of_nodup [Fintype α] (l
 : List α) (h : Nodup l) (h' : forall x : α, l != [x]) : support (formPerm l) = 
l.toFinset
· 使用定理 `List.toFinset_card_of_nodup`：List.toFinset_card_of_nodup {l : List α} (h
 : l.Nodup) : #l.toFinset = l.length

--- 原说明 ---
There are permutations with cycleType `m` if and only if
  its sum is at most `Fintype.card α` and its members are at least 2.
-/
theorem Equiv.Perm.exists_with_cycleType_iff {m : Multiset ℕ} :
    (∃ g : Equiv.Perm α, g.cycleType = m) ↔
      (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) := by
  constructor
  · -- empty case
    intro h
    obtain ⟨g, hg⟩ := h
    constructor
    · rw [← hg, Equiv.Perm.sum_cycleType]
      exact (Equiv.Perm.support g).card_le_univ
    · intro a
      rw [← hg]
      exact Equiv.Perm.two_le_of_mem_cycleType
  · rintro ⟨hc, h2c⟩
    have hc' : m.toList.sum ≤ Fintype.card α := by
      simp only [Multiset.sum_toList]
      exact hc
    obtain ⟨p, hp_length, hp_nodup, hp_disj⟩ := List.exists_pw_disjoint_with_card hc'
    use List.prod (List.map (fun l => List.formPerm l) p)
    have hp2 : ∀ x ∈ p, 2 ≤ x.length := by
      intro x hx
      apply h2c x.length
      rw [← Multiset.mem_toList, ← hp_length, List.mem_map]
      exact ⟨x, hx, rfl⟩
    rw [Equiv.Perm.cycleType_eq _ rfl]
    · -- lengths
      rw [← Multiset.coe_toList m]
      apply congr_arg
      rw [List.map_map]; rw [← hp_length]
      apply List.map_congr_left
      intro x hx; simp only [Function.comp_apply]
      rw [List.support_formPerm_of_nodup x (hp_nodup x hx)]
      · -- length
        rw [List.toFinset_card_of_nodup (hp_nodup x hx)]
      · -- length >= 1
        grind
    · -- cycles
      simpa using fun a b ↦ List.isCycle_formPerm (hp_nodup a b) (hp2 a b)
    · -- disjoint
      rw [List.pairwise_map]
      apply List.Pairwise.imp_of_mem _ hp_disj
      intro a b ha hb hab
      rw [List.formPerm_disjoint_iff (hp_nodup a ha) (hp_nodup b hb) (hp2 a ha) (hp2 b hb)]
      exact hab
