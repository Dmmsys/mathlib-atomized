/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Aaron Anderson
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Antichain
public import Mathlib.Order.OrderIsoNat

/-!
# Well quasi-orders

A well quasi-order (WQO) is a relation such that any infinite sequence contains an infinite
subsequence of related elements. For a preorder, this is equivalent to having a well-founded order
with no infinite antichains.

## Main definitions

* `WellQuasiOrdered`: a predicate for WQO unbundled relations
* `WellQuasiOrderedLE`: a typeclass for a bundled WQO `≤` relation

## Tags

wqo, pwo, well quasi-order, partial well order, dickson order
-/

@[expose] public section

variable {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}

/-- A well quasi-order or WQO is a relation such that any infinite sequence contains an infinite
monotonic subsequence, or equivalently, two elements `f m` and `f n` with `m < n` and
`r (f m) (f n)`.

For a preorder, this is equivalent to having a well-founded order with no infinite antichains.

Despite the nomenclature, we don't require the relation to be preordered. Moreover, a well
quasi-order will not in general be a well-order. -/
/-
**WellQuasiOrdered** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WellQuasiOrdered (r : α -> α -> Prop) : Prop
参数：r : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A well quasi-order or WQO is a relation such that any infinite sequence contains
 an infinite
monotonic subsequence, or equivalently, two elements `f m` and `f n` with `m < n
` and
`r (f m) (f n)`.

For a preorder, this is equivalent to having a well-founded order with no infini
te antichains.

Despite the nomenclature, we don't require the relation to be preordered. Moreov
er, a well
quasi-order will not in general be a well-order.
-/
def WellQuasiOrdered (r : α → α → Prop) : Prop :=
  ∀ f : ℕ → α, ∃ m n : ℕ, m < n ∧ r (f m) (f n)
/-
**wellQuasiOrdered_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellQuasiOrdered_of_isEmpty [IsEmpty α] (r : α -> α -> Prop) : WellQuasiOr
dered r
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wellQuasiOrdered_of_isEmpty [IsEmpty α] (r : α → α → Prop) : WellQuasiOrdered r :=
  fun f ↦ isEmptyElim (f 0)
/-
**IsAntichain.finite_of_wellQuasiOrdered** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAntichain.finite_of_wellQuasiOrdered {s : Set α} (hs : IsAntichain r s) 
(hr : WellQuasiOrdered r) : s.Finite
参数：hs : IsAntichain r s；hr : WellQuasiOrdered r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `IsAntichain.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntic
hain r s → ∀ {a b : α}, a ∈ s → b ∈ s → r a b → a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem IsAntichain.finite_of_wellQuasiOrdered {s : Set α} (hs : IsAntichain r s)
    (hr : WellQuasiOrdered r) : s.Finite := by
  by_contra! hi
  obtain ⟨m, n, hmn, h⟩ := hr fun n => hi.natEmbedding _ n
  exact hmn.ne ((hi.natEmbedding _).injective <| Subtype.val_injective <|
    hs.eq (hi.natEmbedding _ m).2 (hi.natEmbedding _ n).2 h)
/-
**Finite.wellQuasiOrdered** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.wellQuasiOrdered (r : α -> α -> Prop) [Finite α] [Std.Refl r] : Wel
lQuasiOrdered r
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.exists_lt_map_eq_of_forall_mem`：∀ {α : Type u_2} {β : Type u_
3} [inst : LinearOrder α] {t : Set β} {f : α → β} [Infinite α],   (∀ (a : α), f 
a ∈ t) → t.Finite → ∃ a b, a < …
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem Finite.wellQuasiOrdered (r : α → α → Prop) [Finite α] [Std.Refl r] :
    WellQuasiOrdered r := by
  intro f
  obtain ⟨m, n, h, hf⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem (f := f)
    fun _ ↦ Set.mem_univ _
  exact ⟨m, n, h, hf ▸ refl _⟩
/-
**WellQuasiOrdered.exists_monotone_subseq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellQuasiOrdered.exists_monotone_subseq [IsPreorder α r] (h : WellQuasiOrd
ered r) (f : Nat -> α) : exists g : Nat ↪o Nat, forall m n, m <= n -> r (f (g m)
) (f (g n))
参数：h : WellQuasiOrdered r；f : Nat -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_increasing_or_nonincreasing_subseq`：exists_increasing_or_nonincre
asing_subseq (r : α -> α -> Prop) [IsTrans α r] (f : Nat -> α) : exists g : Nat 
↪o Nat, (forall m n : Nat, m < …
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `refl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Refl r] (a : α), r a a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
-/
theorem WellQuasiOrdered.exists_monotone_subseq [IsPreorder α r] (h : WellQuasiOrdered r)
    (f : ℕ → α) : ∃ g : ℕ ↪o ℕ, ∀ m n, m ≤ n → r (f (g m)) (f (g n)) := by
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq r f
  · refine ⟨g, fun m n hle => ?_⟩
    obtain hlt | rfl := hle.lt_or_eq
    exacts [h1 m n hlt, refl_of r _]
  · obtain ⟨m, n, hlt, hle⟩ := h (f ∘ g)
    cases h2 m n hlt hle
/-
**wellQuasiOrdered_iff_exists_monotone_subseq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellQuasiOrdered_iff_exists_monotone_subseq [IsPreorder α r] : WellQuasiOr
dered r ↔ forall f : Nat -> α, exists g : Nat ↪o Nat, forall m n : Nat, m <= n -
> r (f (g m)) (f (g n))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellQuasiOrdered.exists_monotone_subseq`：WellQuasiOrdered.exists_monoton
e_subseq [IsPreorder α r] (h : WellQuasiOrdered r) (f : Nat -> α) : exists g : N
at ↪o Nat, forall m n, m <= n…
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
· 使用定理 `Nat.zero_lt_one`：0 < 1
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem wellQuasiOrdered_iff_exists_monotone_subseq [IsPreorder α r] :
    WellQuasiOrdered r ↔ ∀ f : ℕ → α, ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) := by
  constructor <;> intro h f
  · exact h.exists_monotone_subseq f
  · obtain ⟨g, gmon⟩ := h f
    exact ⟨_, _, g.strictMono Nat.zero_lt_one, gmon _ _ (Nat.zero_le 1)⟩
/-
**WellQuasiOrdered.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellQuasiOrdered.prod [IsPreorder α r] (hr : WellQuasiOrdered r) (hs : Wel
lQuasiOrdered s) : WellQuasiOrdered fun a b : α × β => r a.1 b.1 ∧ s a.2 b.2
参数：hr : WellQuasiOrdered r；hs : WellQuasiOrdered s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellQuasiOrdered.exists_monotone_subseq`：WellQuasiOrdered.exists_monoton
e_subseq [IsPreorder α r] (h : WellQuasiOrdered r) (f : Nat -> α) : exists g : N
at ↪o Nat, forall m n, m <= n…
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem WellQuasiOrdered.prod [IsPreorder α r] (hr : WellQuasiOrdered r) (hs : WellQuasiOrdered s) :
    WellQuasiOrdered fun a b : α × β ↦ r a.1 b.1 ∧ s a.2 b.2 := by
  intro f
  obtain ⟨g, h₁⟩ := hr.exists_monotone_subseq (Prod.fst ∘ f)
  obtain ⟨m, n, h, hf⟩ := hs (Prod.snd ∘ f ∘ g)
  exact ⟨g m, g n, g.strictMono h, h₁ _ _ h.le, hf⟩

/-- A version of **Dickson's lemma**: the Pi type `∀ i : ι, α i` is well-quasi-ordered when `ι` is
finite and each `σ i` is well-quasi-ordered. See `Set.PartiallyWellOrderedOn.pi` for the finite
product of well-quasi-ordered sets and `Pi.wellQuasiOrderedLE` when the relation is `≤`. -/
/-
**WellQuasiOrdered.pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellQuasiOrdered.pi {ι : Type*} {α : ι -> Type*} [Finite ι] {r : forall i,
 (α i -> α i -> Prop)} [forall i, IsPreorder (α i) (r i)] (hr : forall i, WellQu
asiOrdered (r i)) : WellQuasiOrdered fun a b : forall i, α i => forall i, r i (a
 i) (b i)
参数：α i -> α i -> Prop；α i；r i；hr : forall i, WellQuasiOrdered (r i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `WellQuasiOrdered.exists_monotone_subseq`：WellQuasiOrdered.exists_monoton
e_subseq [IsPreorder α r] (h : WellQuasiOrdered r) (f : Nat -> α) : exists g : N
at ↪o Nat, forall m n, m <= n…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.forall_mem_cons`：forall_mem_cons (h : a ∉ s) (p : α -> Prop) : (f
orall x, x in cons a s h -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `RelEmbedding.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α
 → Prop} {s : β → β → Prop}, RelHomClass (r ↪r s) r s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wellQuasiOrdered_iff_exists_monotone_subseq`：wellQuasiOrdered_iff_exists
_monotone_subseq [IsPreorder α r] : WellQuasiOrdered r ↔ forall f : Nat -> α, ex
ists g : Nat ↪o Nat, forall m n :…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
A version of **Dickson's lemma**: the Pi type `∀ i : ι, α i` is well-quasi-order
ed when `ι` is
finite and each `σ i` is well-quasi-ordered. See `Set.PartiallyWellOrderedOn.pi`
 for the finite
product of well-quasi-ordered sets and `Pi.wellQuasiOrderedLE` when the relation
 is `≤`.
-/
theorem WellQuasiOrdered.pi {ι : Type*} {α : ι → Type*} [Finite ι] {r : ∀ i, (α i → α i → Prop)}
    [∀ i, IsPreorder (α i) (r i)] (hr : ∀ i, WellQuasiOrdered (r i)) :
    WellQuasiOrdered fun a b : ∀ i, α i => ∀ i, r i (a i) (b i) := by
  have := Fintype.ofFinite ι
  have : IsPreorder (∀ i, α i) (fun a b : ∀ i, α i => ∀ i, r i (a i) (b i)) :=
    { refl a i := refl (a i)
      trans a b c hab hbc i := _root_.trans (hab i) (hbc i) }
  suffices ∀ (s : Finset ι) (f : ℕ → ∀ i, α i),
    ∃ g : ℕ ↪o ℕ, ∀ ⦃a b : ℕ⦄, a ≤ b → ∀ i, i ∈ s → r i ((f ∘ g) a i) ((f ∘ g) b i) by
    rw [wellQuasiOrdered_iff_exists_monotone_subseq]
    intro f
    simpa only [Finset.mem_univ, true_imp_iff] using! this Finset.univ f
  refine Finset.cons_induction ?_ ?_
  · intro f
    exists RelEmbedding.refl (· ≤ ·)
    simp only [IsEmpty.forall_iff, imp_true_iff, Finset.notMem_empty]
  · intro i s hi ih f
    obtain ⟨g, hg⟩ := (hr i).exists_monotone_subseq (f · i)
    obtain ⟨g', hg'⟩ := ih (f ∘ g)
    refine ⟨g'.trans g, fun a b hab => (Finset.forall_mem_cons _ _).2 ?_⟩
    exact ⟨hg _ _ (OrderHomClass.mono g' hab), hg' hab⟩
/-
**RelIso.wellQuasiOrdered_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelIso.wellQuasiOrdered_iff {α β} {r : α -> α -> Prop} {s : β -> β -> Prop
} (f : r ≃r s) : WellQuasiOrdered r ↔ WellQuasiOrdered s
参数：f : r ≃r s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.arrowCongr_apply`：∀ {α₁ : Sort u_1} {β₁ : Sort u_2} {α₂ : Sort u_3
} {β₂ : Sort u_4} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (f : α₁ → β₁) (a : α₂),   (e₁.ar
rowCongr e₂)…
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem RelIso.wellQuasiOrdered_iff {α β} {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) :
    WellQuasiOrdered r ↔ WellQuasiOrdered s := by
  apply (Equiv.arrowCongr (.refl ℕ) f).forall_congr
  congr! with g a b
  simp [f.map_rel_iff]
/-
**WellQuasiOrdered.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellQuasiOrdered.of_surjective {α β} {r : α -> α -> Prop} {s : β -> β -> P
rop} (h : WellQuasiOrdered r) (f : r ->r s) (hf : Function.Surjective f) : WellQ
uasiOrdered s
参数：h : WellQuasiOrdered r；f : r ->r s；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
· 使用定理 `RelHom.map_rel`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : 
β → β → Prop} (f : r →r s) {a b : α}, r a b → s (f a) (f b)
-/
theorem WellQuasiOrdered.of_surjective {α β} {r : α → α → Prop}
    {s : β → β → Prop} (h : WellQuasiOrdered r) (f : r →r s) (hf : Function.Surjective f) :
    WellQuasiOrdered s := by
  intro seq
  have ⟨_, _, hle, hr⟩ := h (Function.surjInv hf ∘ seq)
  exact ⟨_, _, hle, by simpa [Function.surjInv_eq] using f.map_rel hr⟩

/-- A typeclass for an order with a well-quasi-ordered `≤` relation.

Note that this is unlike `WellFoundedLT`, which instead takes a `<` relation. -/
@[mk_iff wellQuasiOrderedLE_def]
/-
**WellQuasiOrderedLE** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [LE α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass for an order with a well-quasi-ordered `≤` relation.

Note that this is unlike `WellFoundedLT`, which instead takes a `<` relation.
-/
class WellQuasiOrderedLE (α : Type*) [LE α] where
  wqo : @WellQuasiOrdered α (· ≤ ·)
/-
**wellQuasiOrdered_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellQuasiOrdered_le [LE α] [h : WellQuasiOrderedLE α] : @WellQuasiOrdered 
α (· <= ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellQuasiOrderedLE.wqo`：∀ {α : Type u_3} {inst : LE α} [self : WellQuasi
OrderedLE α], WellQuasiOrdered fun x1 x2 => x1 ≤ x2
-/
theorem wellQuasiOrdered_le [LE α] [h : WellQuasiOrderedLE α] : @WellQuasiOrdered α (· ≤ ·) :=
  h.wqo
/-
**OrderIso.wellQuasiOrderedLE_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.wellQuasiOrderedLE_iff {α β} [LE α] [LE β] (f : α ≃o β) : WellQua
siOrderedLE α ↔ WellQuasiOrderedLE β
参数：f : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelIso.wellQuasiOrdered_iff`：RelIso.wellQuasiOrdered_iff {α β} {r : α ->
 α -> Prop} {s : β -> β -> Prop} (f : r ≃r s) : WellQuasiOrdered r ↔ WellQuasiOr
dered s
-/
theorem OrderIso.wellQuasiOrderedLE_iff {α β} [LE α] [LE β] (f : α ≃o β) :
    WellQuasiOrderedLE α ↔ WellQuasiOrderedLE β := by
  simpa [wellQuasiOrderedLE_def] using f.wellQuasiOrdered_iff

section Preorder
variable [Preorder α]

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
/-
**Finite.to_wellQuasiOrderedLE** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finite.to_wellQuasiOrderedLE [Finite α] : WellQuasiOrderedLE α where wqo
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.wellQuasiOrdered`：Finite.wellQuasiOrdered (r : α -> α -> Prop) [F
inite α] [Std.Refl r] : WellQuasiOrdered r
-/
lemma Finite.to_wellQuasiOrderedLE [Finite α] : WellQuasiOrderedLE α where
  wqo := Finite.wellQuasiOrdered _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) WellQuasiOrderedLE.to_wellFoundedLT [WellQuasiOrderedLE α] :
    WellFoundedLT α := by
  rw [WellFoundedLT, isWellFounded_iff, RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun f ↦ ?_⟩
  obtain ⟨a, b, h, hf⟩ := wellQuasiOrdered_le f
  exact (f.map_rel_iff.2 h).not_ge hf
/-
**WellQuasiOrdered.wellFounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellQuasiOrdered.wellFounded {α : Type*} {r : α -> α -> Prop} [IsPreorder 
α r] (h : WellQuasiOrdered r) : WellFounded fun a b => r a b ∧ ¬ r b a
参数：h : WellQuasiOrdered r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `refl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Refl r] (a : α), r a a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `trans_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r],
 r a b → r b c → r a c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `WellQuasiOrderedLE.to_wellFoundedLT`：∀ {α : Type u_1} [inst : Preorder α
] [WellQuasiOrderedLE α], WellFoundedLT α
-/
theorem WellQuasiOrdered.wellFounded {α : Type*} {r : α → α → Prop} [IsPreorder α r]
    (h : WellQuasiOrdered r) : WellFounded fun a b ↦ r a b ∧ ¬ r b a := by
  let _ : Preorder α :=
    { le := r
      le_refl := refl_of r
      le_trans := fun _ _ _ => trans_of r }
  have : WellQuasiOrderedLE α := ⟨h⟩
  exact wellFounded_lt
/-
**WellQuasiOrderedLE.finite_of_isAntichain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellQuasiOrderedLE.finite_of_isAntichain [WellQuasiOrderedLE α] {s : Set α
} (h : IsAntichain (· <= ·) s) : s.Finite
参数：h : IsAntichain (· <= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.finite_of_wellQuasiOrdered`：IsAntichain.finite_of_wellQuasiO
rdered {s : Set α} (hs : IsAntichain r s) (hr : WellQuasiOrdered r) : s.Finite
· 使用定理 `wellQuasiOrdered_le`：wellQuasiOrdered_le [LE α] [h : WellQuasiOrderedLE 
α] : @WellQuasiOrdered α (· <= ·)
-/
theorem WellQuasiOrderedLE.finite_of_isAntichain [WellQuasiOrderedLE α] {s : Set α}
    (h : IsAntichain (· ≤ ·) s) : s.Finite :=
  h.finite_of_wellQuasiOrdered wellQuasiOrdered_le

/-- A preorder is well quasi-ordered iff it's well-founded and has no infinite antichains. -/
/-
**wellQuasiOrderedLE_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellQuasiOrderedLE_iff : WellQuasiOrderedLE α ↔ WellFoundedLT α ∧ forall s
 : Set α, IsAntichain (· <= ·) s -> s.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellQuasiOrderedLE.to_wellFoundedLT`：∀ {α : Type u_1} [inst : Preorder α
] [WellQuasiOrderedLE α], WellFoundedLT α
· 使用定理 `WellQuasiOrderedLE.finite_of_isAntichain`：WellQuasiOrderedLE.finite_of_i
sAntichain [WellQuasiOrderedLE α] {s : Set α} (h : IsAntichain (· <= ·) s) : s.F
inite
· 使用定理 `exists_increasing_or_nonincreasing_subseq`：exists_increasing_or_nonincre
asing_subseq (r : α -> α -> Prop) [IsTrans α r] (f : Nat -> α) : exists g : Nat 
↪o Nat, (forall m n : Nat, m < …
· 使用定理 `instIsTransGt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 < x1
· 使用定理 `RelEmbedding.not_wellFounded`：not_wellFounded (f : ((· > ·) : Nat -> Nat
 -> Prop) ↪r r) : ¬WellFounded r
· 使用定理 `instIsStrictOrderLt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x1 < x2
· 使用定理 `Nat.instTrichotomousLt`：Std.Trichotomous fun x1 x2 => x1 < x2
· 使用定理 `instAsymmGt`：∀ {α : Type u} [inst : Preorder α], Std.Asymm fun x1 x2 => 
x2 < x1
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
· 使用定理 `Set.infinite_range_of_injective`：infinite_range_of_injective [Infinite α
] {f : α -> β} (hi : Injective f) : (range f).Infinite
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
A preorder is well quasi-ordered iff it's well-founded and has no infinite antic
hains.
-/
theorem wellQuasiOrderedLE_iff :
    WellQuasiOrderedLE α ↔ WellFoundedLT α ∧ ∀ s : Set α, IsAntichain (· ≤ ·) s → s.Finite := by
  refine ⟨fun h ↦ ⟨h.to_wellFoundedLT, fun s ↦ h.finite_of_isAntichain⟩,
    fun ⟨hwf, hc⟩ ↦ ⟨fun f ↦ ?_⟩⟩
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq (· > ·) f
  · exfalso
    apply RelEmbedding.not_wellFounded _ hwf.wf
    exact (RelEmbedding.ofMonotone _ h1).swap
  · contrapose! hc
    refine ⟨Set.range (f ∘ g), ?_, ?_⟩
    · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ _ hf
      obtain h | rfl | h := lt_trichotomy m n
      · exact hc _ _ (g.strictMono h) hf
      · contradiction
      · exact h2 _ _ h (lt_of_le_not_ge hf (hc _ _ (g.strictMono h)))
    · refine Set.infinite_range_of_injective fun m n (hf : f (g m) = f (g n)) ↦ ?_
      obtain h | rfl | h := lt_trichotomy m n <;>
        (first | rfl | cases (hf ▸ hc _ _ (g.strictMono h)) le_rfl)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WellQuasiOrderedLE α] [Preorder β] [WellQuasiOrderedLE β] : WellQuasiOrderedLE (α × β) :=
  ⟨wellQuasiOrdered_le.prod wellQuasiOrdered_le⟩
/-
**Monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective** 是 Mathlib 中的
一个定理，位于命名空间 ``。
形式化陈述：Monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective [Preorder 
β] [WellQuasiOrderedLE α] {f : α -> β} (mono : Monotone f) (hf : Function.Surjec
tive f) : WellQuasiOrderedLE β
参数：mono : Monotone f；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellQuasiOrdered.of_surjective`：WellQuasiOrdered.of_surjective {α β} {r 
: α -> α -> Prop} {s : β -> β -> Prop} (h : WellQuasiOrdered r) (f : r ->r s) (h
f : Function.Surject…
· 使用定理 `wellQuasiOrdered_le`：wellQuasiOrdered_le [LE α] [h : WellQuasiOrderedLE 
α] : @WellQuasiOrdered α (· <= ·)
-/
theorem Monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective [Preorder β]
    [WellQuasiOrderedLE α] {f : α → β} (mono : Monotone f) (hf : Function.Surjective f) :
    WellQuasiOrderedLE β :=
  ⟨wellQuasiOrdered_le.of_surjective ⟨_, (mono ·)⟩ hf⟩
/-
**OrderHom.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective** 是 Mathlib 中的
一个定理，位于命名空间 ``。
形式化陈述：OrderHom.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective [Preorder 
β] [WellQuasiOrderedLE α] (f : α ->o β) (hf : Function.Surjective f) : WellQuasi
OrderedLE β
参数：f : α ->o β；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective`：Monoton
e.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective [Preorder β] [WellQuasi
OrderedLE α] {f : α -> β} (mono : Monotone f) (hf : F…
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
theorem OrderHom.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective [Preorder β]
    [WellQuasiOrderedLE α] (f : α →o β) (hf : Function.Surjective f) :
    WellQuasiOrderedLE β :=
  f.monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective hf

end Preorder

section LinearOrder
variable [LinearOrder α]

/-- A linear WQO is the same thing as a well-order. -/
/-
**wellQuasiOrderedLE_iff_wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellQuasiOrderedLE_iff_wellFoundedLT : WellQuasiOrderedLE α ↔ WellFoundedL
T α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wellQuasiOrderedLE_iff`：wellQuasiOrderedLE_iff : WellQuasiOrderedLE α ↔ 
WellFoundedLT α ∧ forall s : Set α, IsAntichain (· <= ·) s -> s.Finite
· 使用定理 `and_iff_left_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ a) ↔ a → b
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
· 使用定理 `IsAntichain.subsingleton`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α
} [Std.Trichotomous r], IsAntichain r s → s.Subsingleton

--- 原说明 ---
A linear WQO is the same thing as a well-order.
-/
theorem wellQuasiOrderedLE_iff_wellFoundedLT : WellQuasiOrderedLE α ↔ WellFoundedLT α := by
  rw [wellQuasiOrderedLE_iff, and_iff_left_iff_imp]
  exact fun _ s hs ↦ hs.subsingleton.finite
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : WellFoundedLT α] : WellQuasiOrderedLE α :=
  wellQuasiOrderedLE_iff_wellFoundedLT.mpr h

end LinearOrder

/-- A version of **Dickson's lemma**. See `Set.IsPWO.pi` for the finite product of
well-quasi-ordered sets. -/
/-
**Pi.wellQuasiOrderedLE** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.wellQuasiOrderedLE {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α 
i)] [h : forall i, WellQuasiOrderedLE (α i)] [Finite ι] : WellQuasiOrderedLE (fo
rall i, α i)
参数：α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WellQuasiOrdered.pi`：WellQuasiOrdered.pi {ι : Type*} {α : ι -> Type*} [F
inite ι] {r : forall i, (α i -> α i -> Prop)} [forall i, IsPreorder (α i) (r i)]
 (hr : fo…
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
· 使用定理 `WellQuasiOrderedLE.wqo`：∀ {α : Type u_3} {inst : LE α} [self : WellQuasi
OrderedLE α], WellQuasiOrdered fun x1 x2 => x1 ≤ x2

--- 原说明 ---
A version of **Dickson's lemma**. See `Set.IsPWO.pi` for the finite product of
well-quasi-ordered sets.
-/
instance Pi.wellQuasiOrderedLE {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)]
    [h : ∀ i, WellQuasiOrderedLE (α i)] [Finite ι] : WellQuasiOrderedLE (∀ i, α i) :=
  ⟨WellQuasiOrdered.pi fun i => (h i).wqo⟩
