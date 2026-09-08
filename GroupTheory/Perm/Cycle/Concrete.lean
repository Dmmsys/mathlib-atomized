/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.List.Cycle
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.List

/-!

# Properties of cyclic permutations constructed from lists/cycles

In the following, `{α : Type*} [Fintype α] [DecidableEq α]`.

## Main definitions

* `Cycle.formPerm`: the cyclic permutation created by looping over a `Cycle α`
* `Equiv.Perm.toList`: the list formed by iterating application of a permutation
* `Equiv.Perm.toCycle`: the cycle formed by iterating application of a permutation
* `Equiv.Perm.isoCycle`: the equivalence between cyclic permutations `f : Perm α`
  and the terms of `Cycle α` that correspond to them
* `Equiv.Perm.isoCycle'`: the same equivalence as `Equiv.Perm.isoCycle`
  but with evaluation via choosing over fintypes
* The notation `c[1, 2, 3]` to emulate notation of cyclic permutations `(1 2 3)`
* A `Repr` instance for any `Perm α`, by representing the `Finset` of
  `Cycle α` that correspond to the cycle factors.

## Main results

* `List.isCycle_formPerm`: a nontrivial list without duplicates, when interpreted as
  a permutation, is cyclic
* `Equiv.Perm.IsCycle.existsUnique_cycle`: there is only one nontrivial `Cycle α`
  corresponding to each cyclic `f : Perm α`

## Implementation details

The forward direction of `Equiv.Perm.isoCycle'` uses `Fintype.choose` of the uniqueness
result, relying on the `Fintype` instance of a `Cycle.Nodup` subtype.
It is unclear if this works faster than the `Equiv.Perm.toCycle`, which relies
on recursion over `Finset.univ`.

-/

@[expose] public section


open Equiv Equiv.Perm List

variable {α : Type*}

namespace List

variable [DecidableEq α] {l l' : List α}

/-
**List.formPerm_disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_disjoint_iff (hl : Nodup l) (hl' : Nodup l') (hn : 2 <= l.length)
 (hn' : 2 <= l'.length) : Perm.Disjoint (formPerm l) (formPerm l') ↔ l.Disjoint 
l'
参数：hl : Nodup l；hl' : Nodup l'；hn : 2 <= l.length；hn' : 2 <= l'.length。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.disjoint_iff_eq_or_eq`：disjoint_iff_eq_or_eq : Disjoint f g ↔
 forall x : α, f x = x ∨ g x = x
· 使用定理 `List.Disjoint.eq_1`：∀ {α : Type u_1} (l₁ l₂ : List α), l₁.Disjoint l₂ = 
∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂ → False
· 使用定理 `List.formPerm_apply_mem_eq_self_iff`：formPerm_apply_mem_eq_self_iff (hl 
: Nodup l) (x : α) (hx : x in l) : formPerm l x = x ↔ length l <= 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.formPerm_apply_of_notMem`：formPerm_apply_of_notMem (h : x ∉ l) : fo
rmPerm l x = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
theorem formPerm_disjoint_iff (hl : Nodup l) (hl' : Nodup l') (hn : 2 ≤ l.length)
    (hn' : 2 ≤ l'.length) : Perm.Disjoint (formPerm l) (formPerm l') ↔ l.Disjoint l' := by
  rw [disjoint_iff_eq_or_eq, List.Disjoint]
  constructor
  · rintro h x hx hx'
    specialize h x
    rw [formPerm_apply_mem_eq_self_iff _ hl _ hx, formPerm_apply_mem_eq_self_iff _ hl' _ hx'] at h
    lia
  · intro h x
    by_cases hx : x ∈ l
    on_goal 1 => by_cases hx' : x ∈ l'
    · exact (h hx hx').elim
    all_goals have := List.formPerm_apply_of_notMem ‹_›; tauto
/-
**List.isCycle_formPerm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isCycle_formPerm (hl : Nodup l) (hn : 2 <= l.length) : IsCycle (formPerm l
)
参数：hl : Nodup l；hn : 2 <= l.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false`：¬False
· 使用定理 `List.formPerm_apply_mem_ne_self_iff`：formPerm_apply_mem_ne_self_iff (hl 
: Nodup l) (x : α) (hx : x in l) : formPerm l x != x ↔ 2 <= l.length
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.mem_of_formPerm_apply_ne`：mem_of_formPerm_apply_ne (h : l.formPerm 
x != x) : x in l
· 使用定理 `List.getElem_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ i,
 ∃ (h : i < l.length), l[i] = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `List.formPerm_pow_apply_head`：formPerm_pow_apply_head (x : α) (l : List 
α) (h : Nodup (x :: l)) (n : Nat) : (formPerm (x :: l) ^ n) x = (x :: l)[(n % (x
 :: l).length)]'(N…
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isCycle_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) : IsCycle (formPerm l) := by
  rcases l with - | ⟨x, l⟩
  · norm_num at hn
  induction l generalizing x with
  | nil => norm_num at hn
  | cons y l =>
    use x
    constructor
    · rwa [formPerm_apply_mem_ne_self_iff _ hl _ mem_cons_self]
    · intro w hw
      have : w ∈ x::y::l := mem_of_formPerm_apply_ne hw
      obtain ⟨k, hk, rfl⟩ := getElem_of_mem this
      use k
      simp only [zpow_natCast, formPerm_pow_apply_head _ _ hl k, Nat.mod_eq_of_lt hk]
/-
**List.pairwise_sameCycle_formPerm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pairwise_sameCycle_formPerm (hl : Nodup l) (hn : 2 <= l.length) : Pairwise
 l.formPerm.SameCycle l
参数：hl : Nodup l；hn : 2 <= l.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Pairwise.imp_mem`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},
 List.Pairwise R l ↔ List.Pairwise (fun x y => x ∈ l → y ∈ l → R x y) l
· 使用定理 `List.pairwise_of_forall`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α
}, (∀ (x y : α), R x y) → List.Pairwise R l
· 使用定理 `Equiv.Perm.IsCycle.sameCycle`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y :
 α}, f.IsCycle → f x ≠ x → f y ≠ y → f.SameCycle x y
· 使用定理 `List.isCycle_formPerm`：isCycle_formPerm (hl : Nodup l) (hn : 2 <= l.leng
th) : IsCycle (formPerm l)
· 使用定理 `List.formPerm_apply_mem_ne_self_iff`：formPerm_apply_mem_ne_self_iff (hl 
: Nodup l) (x : α) (hx : x in l) : formPerm l x != x ↔ 2 <= l.length
-/
theorem pairwise_sameCycle_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) :
    Pairwise l.formPerm.SameCycle l :=
  Pairwise.imp_mem.mpr
    (pairwise_of_forall fun _ _ hx hy =>
      (isCycle_formPerm hl hn).sameCycle ((formPerm_apply_mem_ne_self_iff _ hl _ hx).mpr hn)
        ((formPerm_apply_mem_ne_self_iff _ hl _ hy).mpr hn))
/-
**List.cycleOf_formPerm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cycleOf_formPerm (hl : Nodup l) (hn : 2 <= l.length) (x) : cycleOf l.attac
h.formPerm x = l.attach.formPerm
参数：hl : Nodup l；hn : 2 <= l.length；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_attach`：∀ {α : Type u_1} {l : List α}, l.attach.length = l.l
ength
· 使用定理 `List.nodup_attach`：nodup_attach {l : List α} : Nodup (attach l) ↔ Nodup 
l
· 使用定理 `Equiv.Perm.IsCycle.cycleOf_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {x : 
α} [inst : DecidableRel f.SameCycle], f.IsCycle → f x ≠ x → f.cycleOf x = f
· 使用定理 `List.isCycle_formPerm`：isCycle_formPerm (hl : Nodup l) (hn : 2 <= l.leng
th) : IsCycle (formPerm l)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.formPerm_apply_mem_ne_self_iff`：formPerm_apply_mem_ne_self_iff (hl 
: Nodup l) (x : α) (hx : x in l) : formPerm l x != x ↔ 2 <= l.length
· 使用定理 `List.mem_attach`：∀ {α : Type u_1} (l : List α) (x : { x // x ∈ l }), x ∈
 l.attach
-/
theorem cycleOf_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) (x) :
    cycleOf l.attach.formPerm x = l.attach.formPerm :=
  have hn : 2 ≤ l.attach.length := by rwa [← length_attach] at hn
  have hl : l.attach.Nodup := by rwa [← nodup_attach] at hl
  (isCycle_formPerm hl hn).cycleOf_eq
    ((formPerm_apply_mem_ne_self_iff _ hl _ (mem_attach _ _)).mpr hn)
/-
**List.cycleType_formPerm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cycleType_formPerm (hl : Nodup l) (hn : 2 <= l.length) : cycleType l.attac
h.formPerm = {l.length}
参数：hl : Nodup l；hn : 2 <= l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType_eq`：cycleType_eq {σ : Perm α} (l : List (Perm α)) (
h0 : l.prod = σ) (h1 : forall σ : Perm α, σ in l -> σ.IsCycle) (h2 : l.Pairwise 
Disjoint) : σ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `List.isCycle_formPerm`：isCycle_formPerm (hl : Nodup l) (hn : 2 <= l.leng
th) : IsCycle (formPerm l)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.nodup_attach`：nodup_attach {l : List α} : Nodup (attach l) ↔ Nodup 
l
· 使用定理 `List.length_attach`：∀ {α : Type u_1} {l : List α}, l.attach.length = l.l
ength
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `List.support_formPerm_of_nodup`：support_formPerm_of_nodup [Fintype α] (l
 : List α) (h : Nodup l) (h' : forall x : α, l != [x]) : support (formPerm l) = 
l.toFinset
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `List.card_toFinset`：List.card_toFinset : #l.toFinset = l.dedup.length
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.dedup_eq_self`：dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l
-/
theorem cycleType_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) :
    cycleType l.attach.formPerm = {l.length} := by
  rw [← length_attach] at hn
  rw [← nodup_attach] at hl
  rw [cycleType_eq [l.attach.formPerm]]
  · simp only [map, Function.comp_apply]
    rw [support_formPerm_of_nodup _ hl, card_toFinset, dedup_eq_self.mpr hl]
    · simp
    · intro x h
      simp [h] at hn
  · simp
  · simpa using isCycle_formPerm hl hn
  · simp
/-
**List.formPerm_apply_mem_eq_next** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_apply_mem_eq_next (hl : Nodup l) (x : α) (hx : x in l) : formPerm
 l x = next l x hx
参数：hl : Nodup l；x : α；hx : x in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getElem_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ i,
 ∃ (h : i < l.length), l[i] = a
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l
· 使用定理 `List.next_getElem`：next_getElem (l : List α) (h : Nodup l) (i : Nat) (hi
 : i < l.length) : l.next l[i] (get_mem ..) = l[(i + 1) % l.length]'(Nat.mod_lt 
_ (i.ze…
· 使用定理 `List.formPerm_apply_getElem`：formPerm_apply_getElem (xs : List α) (w : N
odup xs) (i : Nat) (h : i < xs.length) : formPerm xs xs[i] = xs[(i + 1) % xs.len
gth]'(Nat.mod_lt …
-/
theorem formPerm_apply_mem_eq_next (hl : Nodup l) (x : α) (hx : x ∈ l) :
    formPerm l x = next l x hx := by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  rw [next_getElem _ hl, formPerm_apply_getElem _ hl]

end List

namespace Cycle

variable [DecidableEq α] (s : Cycle α)

/-- A cycle `s : Cycle α`, given `Nodup s` can be interpreted as an `Equiv.Perm α`
where each element in the list is permuted to the next one, defined as `formPerm`.
-/
/-
**Cycle.formPerm** 是 Mathlib 中的一个定义，位于命名空间 `Cycle`。
形式化陈述：formPerm : forall s : Cycle α, Nodup s -> Equiv.Perm α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cycle `s : Cycle α`, given `Nodup s` can be interpreted as an `Equiv.Perm α`
where each element in the list is permuted to the next one, defined as `formPerm
`.
-/
def formPerm : ∀ s : Cycle α, Nodup s → Equiv.Perm α :=
  fun s => Quotient.hrecOn s (fun l _ => List.formPerm l) fun l₁ l₂ (h : l₁ ~r l₂) => by
    apply Function.hfunext
    · ext
      exact h.nodup_iff
    · intro h₁ h₂ _
      exact heq_of_eq (formPerm_eq_of_isRotated h₁ h)

@[simp]
/-
**Cycle.formPerm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：formPerm_coe (l : List α) (hl : l.Nodup) : formPerm (l : Cycle α) hl = l.f
ormPerm
参数：l : List α；hl : l.Nodup。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem formPerm_coe (l : List α) (hl : l.Nodup) : formPerm (l : Cycle α) hl = l.formPerm :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Cycle.formPerm_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：formPerm_subsingleton (s : Cycle α) (h : Subsingleton s) : formPerm s h.no
dup = 1
参数：s : Cycle α；h : Subsingleton s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cycle.Subsingleton.nodup`：∀ {α : Type u_1} {s : Cycle α}, s.Subsingleton
 → s.Nodup
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem formPerm_subsingleton (s : Cycle α) (h : Subsingleton s) : formPerm s h.nodup = 1 := by
  obtain ⟨s⟩ := s
  simp only [formPerm_coe, mk_eq_coe]
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe] at h
  obtain - | ⟨hd, tl⟩ := s
  · simp
  · simp only [length_eq_zero_iff, add_le_iff_nonpos_left, List.length, nonpos_iff_eq_zero] at h
    simp [h]
/-
**Cycle.isCycle_formPerm** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：isCycle_formPerm (s : Cycle α) (h : Nodup s) (hn : Nontrivial s) : IsCycle
 (formPerm s h)
参数：s : Cycle α；h : Nodup s；hn : Nontrivial s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.isCycle_formPerm`：isCycle_formPerm (hl : Nodup l) (hn : 2 <= l.leng
th) : IsCycle (formPerm l)
· 使用定理 `Cycle.length_nontrivial`：length_nontrivial {s : Cycle α} (h : Nontrivial
 s) : 2 <= length s
-/
theorem isCycle_formPerm (s : Cycle α) (h : Nodup s) (hn : Nontrivial s) :
    IsCycle (formPerm s h) := by
  induction s using Quot.inductionOn
  exact List.isCycle_formPerm h (length_nontrivial hn)
/-
**Cycle.support_formPerm** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：support_formPerm [Fintype α] (s : Cycle α) (h : Nodup s) (hn : Nontrivial 
s) : support (formPerm s h) = s.toFinset
参数：s : Cycle α；h : Nodup s；hn : Nontrivial s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.support_formPerm_of_nodup`：support_formPerm_of_nodup [Fintype α] (l
 : List α) (h : Nodup l) (h' : forall x : α, l != [x]) : support (formPerm l) = 
l.toFinset
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cycle.length_nontrivial`：length_nontrivial {s : Cycle α} (h : Nontrivial
 s) : 2 <= length s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem support_formPerm [Fintype α] (s : Cycle α) (h : Nodup s) (hn : Nontrivial s) :
    support (formPerm s h) = s.toFinset := by
  obtain ⟨s⟩ := s
  refine support_formPerm_of_nodup s h ?_
  rintro _ rfl
  simpa [Nat.succ_le_succ_iff] using length_nontrivial hn

set_option backward.isDefEq.respectTransparency.types false in
/-
**Cycle.formPerm_eq_self_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：formPerm_eq_self_of_notMem (s : Cycle α) (h : Nodup s) (x : α) (hx : x ∉ s
) : formPerm s h x = x
参数：s : Cycle α；h : Nodup s；x : α；hx : x ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.formPerm_apply_of_notMem`：formPerm_apply_of_notMem (h : x ∉ l) : fo
rmPerm l x = x
-/
theorem formPerm_eq_self_of_notMem (s : Cycle α) (h : Nodup s) (x : α) (hx : x ∉ s) :
    formPerm s h x = x := by
  induction s using Quot.inductionOn
  simpa using List.formPerm_apply_of_notMem hx
/-
**Cycle.formPerm_apply_mem_eq_next** 是 Mathlib 中的一个定理，位于命名空间 `Cycle`。
形式化陈述：formPerm_apply_mem_eq_next (s : Cycle α) (h : Nodup s) (x : α) (hx : x in 
s) : formPerm s h x = next s h x hx
参数：s : Cycle α；h : Nodup s；x : α；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.formPerm_apply_mem_eq_next`：formPerm_apply_mem_eq_next (hl : Nodup 
l) (x : α) (hx : x in l) : formPerm l x = next l x hx
-/
theorem formPerm_apply_mem_eq_next (s : Cycle α) (h : Nodup s) (x : α) (hx : x ∈ s) :
    formPerm s h x = next s h x hx := by
  induction s using Quot.inductionOn
  simpa using! List.formPerm_apply_mem_eq_next h _ (by simp_all)

set_option backward.isDefEq.respectTransparency.types false in
nonrec theorem formPerm_reverse (s : Cycle α) (h : Nodup s) :
    formPerm s.reverse (nodup_reverse_iff.mpr h) = (formPerm s h)⁻¹ := by
  induction s using Quot.inductionOn
  simpa using formPerm_reverse _

set_option backward.isDefEq.respectTransparency.types false in
nonrec theorem formPerm_eq_formPerm_iff {α : Type*} [DecidableEq α] {s s' : Cycle α} {hs : s.Nodup}
    {hs' : s'.Nodup} :
    s.formPerm hs = s'.formPerm hs' ↔ s = s' ∨ s.Subsingleton ∧ s'.Subsingleton := by
  rw [Cycle.length_subsingleton_iff, Cycle.length_subsingleton_iff]
  induction s, s' using Quotient.inductionOn₂'
  simpa using formPerm_eq_formPerm_iff hs hs'

end Cycle

namespace Equiv.Perm

section Fintype

variable [Fintype α] [DecidableEq α] (p : Equiv.Perm α) (x : α)

/-- `Equiv.Perm.toList (f : Perm α) (x : α)` generates the list `[x, f x, f (f x), ...]`
until looping. That means when `f x = x`, `toList f x = []`.
-/
/-
**Equiv.Perm.toList** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：toList : List α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.Perm.toList (f : Perm α) (x : α)` generates the list `[x, f x, f (f x), .
..]`
until looping. That means when `f x = x`, `toList f x = []`.
-/
def toList : List α :=
  List.iterate p x (cycleOf p x).support.card

@[simp]
/-
**Equiv.Perm.toList_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：toList_one : toList (1 : Perm α) x = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleOf_one`：cycleOf_one [DecidableRel (1 : Perm α).SameCycle
] (x : α) : cycleOf 1 x = 1
· 使用定理 `Equiv.Perm.support_one`：support_one : (1 : Perm α).support = ∅
· 使用定理 `List.iterate.eq_1`：∀ {α : Type u_1} (f : α → α) (a : α), List.iterate f 
a 0 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toList_one : toList (1 : Perm α) x = [] := by simp [toList, cycleOf_one]

@[simp]
/-
**Equiv.Perm.toList_eq_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：toList_eq_nil_iff {p : Perm α} {x} : toList p x = [] ↔ x ∉ p.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toList_eq_nil_iff {p : Perm α} {x} : toList p x = [] ↔ x ∉ p.support := by simp [toList]

@[simp]
/-
**Equiv.Perm.length_toList** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：length_toList : length (toList p x) = (cycleOf p x).support.card
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_iterate`：length_iterate (f : α -> α) (a : α) (n : Nat) : len
gth (iterate f a n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_toList : length (toList p x) = (cycleOf p x).support.card := by simp [toList]
/-
**Equiv.Perm.toList_ne_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：toList_ne_singleton (y : α) : toList p x != [y]
参数：y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.length_toList`：length_toList : length (toList p x) = (cycleOf
 p x).support.card
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toList_ne_singleton (y : α) : toList p x ≠ [y] := by
  intro H
  simpa [card_support_ne_one] using congr_arg length H
/-
**Equiv.Perm.two_le_length_toList_iff_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `Equ
iv.Perm`。
形式化陈述：two_le_length_toList_iff_mem_support {p : Perm α} {x : α} : 2 <= length (t
oList p x) ↔ x in p.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.length_toList`：length_toList : length (toList p x) = (cycleOf
 p x).support.card
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem two_le_length_toList_iff_mem_support {p : Perm α} {x : α} :
    2 ≤ length (toList p x) ↔ x ∈ p.support := by simp
/-
**Equiv.Perm.length_toList_pos_of_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.P
erm`。
形式化陈述：length_toList_pos_of_mem_support (h : x in p.support) : 0 < length (toList
 p x)
参数：h : x in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.two_le_length_toList_iff_mem_support`：two_le_length_toList_if
f_mem_support {p : Perm α} {x : α} : 2 <= length (toList p x) ↔ x in p.support
-/
theorem length_toList_pos_of_mem_support (h : x ∈ p.support) : 0 < length (toList p x) :=
  zero_lt_two.trans_le (two_le_length_toList_iff_mem_support.mpr h)
/-
**Equiv.Perm.getElem_toList** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：getElem_toList (n : Nat) (hn : n < length (toList p x)) : (toList p x)[n] 
= (p ^ n) x
参数：n : Nat；hn : n < length (toList p x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_iterate`：getElem_iterate (f : α -> α) (a : α) (n : Nat) (i 
: Nat) (h : i < (iterate f a n).length) : (iterate f a n)[i] = f^[i] a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem getElem_toList (n : ℕ) (hn : n < length (toList p x)) :
    (toList p x)[n] = (p ^ n) x := by simp [toList, pull_end]
/-
**Equiv.Perm.toList_getElem_zero** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：toList_getElem_zero (h : x in p.support) : (toList p x)[0]'(length_toList_
pos_of_mem_support _ _ h) = x
参数：h : x in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.Perm.length_toList_pos_of_mem_support`：length_toList_pos_of_mem_su
pport (h : x in p.support) : 0 < length (toList p x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_iterate`：getElem_iterate (f : α -> α) (a : α) (n : Nat) (i 
: Nat) (h : i < (iterate f a n).length) : (iterate f a n)[i] = f^[i] a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toList_getElem_zero (h : x ∈ p.support) :
    (toList p x)[0]'(length_toList_pos_of_mem_support _ _ h) = x := by simp [toList]

variable {p} {x}
/-
**Equiv.Perm.mem_toList_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_toList_iff {y : α} : y in toList p x ↔ SameCycle p x y ∧ x in p.suppor
t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.support_cycleOf_eq_nil_iff`：support_cycleOf_eq_nil_iff [Decid
ableEq α] [Fintype α] : (f.cycleOf x).support = ∅ ↔ x ∉ f.support
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Equiv.Perm.SameCycle.exists_pow_eq_of_mem_support`：∀ {α : Type u_2} {x y
 : α} {f : Equiv.Perm α} [inst : DecidableEq α] [inst_1 : Fintype α],   f.SameCy
cle x y → x ∈ f.support → ∃ i < (f.cycl…
-/
theorem mem_toList_iff {y : α} : y ∈ toList p x ↔ SameCycle p x y ∧ x ∈ p.support := by
  simp only [toList, mem_iterate, iterate_eq_pow, eq_comm (a := y)]
  constructor
  · rintro ⟨n, hx, rfl⟩
    refine ⟨⟨n, rfl⟩, ?_⟩
    contrapose! hx
    rw [← support_cycleOf_eq_nil_iff] at hx
    simp [hx]
  · rintro ⟨h, hx⟩
    simpa using h.exists_pow_eq_of_mem_support hx
/-
**Equiv.Perm.nodup_toList** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：nodup_toList (p : Perm α) (x : α) : Nodup (toList p x)
参数：p : Perm α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.toList_eq_nil_iff`：toList_eq_nil_iff {p : Perm α} {x} : toLis
t p x = [] ↔ x ∉ p.support
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `Equiv.Perm.isCycle_cycleOf`：isCycle_cycleOf (f : Perm α) [DecidableRel f
.SameCycle] (hx : f x != x) : IsCycle (cycleOf f x)
· 使用定理 `List.nodup_iff_injective_getElem`：nodup_iff_injective_getElem {l : List 
α} : Nodup l ↔ Function.Injective (fun i : Fin l.length => l[i.1])
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Fin.mk.injEq`：∀ {n : ℕ} (val : ℕ) (isLt : val < n) (val_1 : ℕ) (isLt_1 :
 val_1 < n), (⟨val, isLt⟩ = ⟨val_1, isLt_1⟩) = (val = val_1)
· 使用定理 `Equiv.Perm.getElem_toList`：getElem_toList (n : Nat) (hn : n < length (to
List p x)) : (toList p x)[n] = (p ^ n) x
· 使用定理 `Equiv.Perm.cycleOf_pow_apply_self`：cycleOf_pow_apply_self (f : Perm α) [
DecidableRel f.SameCycle] (x : α) : forall n : Nat, (cycleOf f x ^ n) x = (f ^ n
) x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.IsCycle.support_pow_of_pos_of_lt_orderOf`：∀ {α : Type u_2} {f
 : Equiv.Perm α} [inst : DecidableEq α] [inst_1 : Fintype α],   f.IsCycle → ∀ {n
 : ℕ}, 0 < n → n < orderOf f → (f ^ n).su…
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Equiv.Perm.cycleOf_apply_self`：cycleOf_apply_self (f : Perm α) [Decidabl
eRel f.SameCycle] (x : α) : cycleOf f x x = f x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Equiv.Perm.IsCycle.orderOf`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : 
DecidableEq α] [inst_1 : Fintype α], f.IsCycle → orderOf f = f.support.card
· 使用定理 `Equiv.Perm.length_toList`：length_toList : length (toList p x) = (cycleOf
 p x).support.card
· 使用定理 `Nat.not_dvd_of_pos_of_lt`：∀ {n m : ℕ}, 0 < n → n < m → ¬m ∣ n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用引理 `pow_inj_mod`：pow_inj_mod {n m : Nat} : x ^ n = x ^ m ↔ n % orderOf x = m
 % orderOf x
（共 39 条，此处仅展示前 30 条）
-/
theorem nodup_toList (p : Perm α) (x : α) : Nodup (toList p x) := by
  by_cases hx : p x = x
  · rw [← notMem_support, ← toList_eq_nil_iff] at hx
    simp [hx]
  have hc : IsCycle (cycleOf p x) := isCycle_cycleOf p hx
  rw [nodup_iff_injective_getElem]
  intro ⟨n, hn⟩ ⟨m, hm⟩
  rw [length_toList, ← hc.orderOf] at hm hn
  rw [← cycleOf_apply_self, ← Ne, ← mem_support] at hx
  simp only [Fin.mk.injEq]
  rw [getElem_toList, getElem_toList, ← cycleOf_pow_apply_self p x n, ←
    cycleOf_pow_apply_self p x m]
  rcases n with - | n <;> rcases m with - | m
  · simp
  · rw [← hc.support_pow_of_pos_of_lt_orderOf m.zero_lt_succ hm, mem_support,
      cycleOf_pow_apply_self] at hx
    simp [hx.symm]
  · rw [← hc.support_pow_of_pos_of_lt_orderOf n.zero_lt_succ hn, mem_support,
      cycleOf_pow_apply_self] at hx
    simp [hx]
  intro h
  have hn' : ¬orderOf (p.cycleOf x) ∣ n.succ := Nat.not_dvd_of_pos_of_lt n.zero_lt_succ hn
  have hm' : ¬orderOf (p.cycleOf x) ∣ m.succ := Nat.not_dvd_of_pos_of_lt m.zero_lt_succ hm
  rw [← hc.support_pow_eq_iff] at hn' hm'
  rw [← Nat.mod_eq_of_lt hn, ← Nat.mod_eq_of_lt hm, ← pow_inj_mod]
  refine support_congr ?_ ?_
  · rw [hm', hn']
  · rw [hm']
    intro y hy
    obtain ⟨k, rfl⟩ := hc.exists_pow_eq (mem_support.mp hx) (mem_support.mp hy)
    rw [← mul_apply, (Commute.pow_pow_self _ _ _).eq, mul_apply, h, ← mul_apply, ← mul_apply,
      (Commute.pow_pow_self _ _ _).eq]
/-
**Equiv.Perm.next_toList_eq_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：next_toList_eq_apply (p : Perm α) (x y : α) (hy : y in toList p x) : next 
(toList p x) y hy = p y
参数：p : Perm α；x y : α；hy : y in toList p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.exists_pow_eq_of_mem_support`：∀ {α : Type u_2} {x y
 : α} {f : Equiv.Perm α} [inst : DecidableEq α] [inst_1 : Fintype α],   f.SameCy
cle x y → x ∈ f.support → ∃ i < (f.cycl…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_toList_iff`：mem_toList_iff {y : α} : y in toList p x ↔ Sa
meCycle p x y ∧ x in p.support
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Equiv.Perm.length_toList`：length_toList : length (toList p x) = (cycleOf
 p x).support.card
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.getElem_toList`：getElem_toList (n : Nat) (hn : n < length (to
List p x)) : (toList p x)[n] = (p ^ n) x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.next.congr_simp`：∀ {α : Type u_1} [inst : DecidableEq α] (l l_1 : L
ist α) (e_l : l = l_1) (x x_1 : α) (e_x : x = x_1) (h : x ∈ l),   l.next x h = l
_1.next x_…
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l
· 使用定理 `List.next_getElem`：next_getElem (l : List α) (h : Nodup l) (i : Nat) (hi
 : i < l.length) : l.next l[i] (get_mem ..) = l[(i + 1) % l.length]'(Nat.mod_lt 
_ (i.ze…
· 使用定理 `Equiv.Perm.nodup_toList`：nodup_toList (p : Perm α) (x : α) : Nodup (toLi
st p x)
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.pow_mod_orderOf_cycleOf_apply`：pow_mod_orderOf_cycleOf_apply 
(f : Perm α) [DecidableRel f.SameCycle] (n : Nat) (x : α) : (f ^ (n % orderOf (c
ycleOf f x))) x = (f ^ n) x
· 使用定理 `Equiv.Perm.IsCycle.orderOf`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : 
DecidableEq α] [inst_1 : Fintype α], f.IsCycle → orderOf f = f.support.card
· 使用定理 `Equiv.Perm.isCycle_cycleOf`：isCycle_cycleOf (f : Perm α) [DecidableRel f
.SameCycle] (hx : f x != x) : IsCycle (cycleOf f x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
-/
theorem next_toList_eq_apply (p : Perm α) (x y : α) (hy : y ∈ toList p x) :
    next (toList p x) y hy = p y := by
  rw [mem_toList_iff] at hy
  obtain ⟨k, hk, hk'⟩ := hy.left.exists_pow_eq_of_mem_support hy.right
  rw [← getElem_toList p x k (by simpa using hk)] at hk'
  simp_rw [← hk']
  rw [next_getElem _ (nodup_toList _ _), getElem_toList, getElem_toList, ← mul_apply, ← pow_succ']
  simp_rw [length_toList]
  rw [← pow_mod_orderOf_cycleOf_apply p (k + 1), IsCycle.orderOf]
  exact isCycle_cycleOf _ (mem_support.mp hy.right)
/-
**Equiv.Perm.toList_pow_apply_eq_rotate** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：toList_pow_apply_eq_rotate (p : Perm α) (x : α) (k : Nat) : p.toList ((p ^
 k) x) = (p.toList x).rotate k
参数：p : Perm α；x : α；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem`：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁
.length l₂.length, l₁[n]? = l₂[n]?) : l₁ = l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.length_toList`：length_toList : length (toList p x) = (cycleOf
 p x).support.card
· 使用定理 `Equiv.Perm.cycleOf_self_apply_pow`：cycleOf_self_apply_pow (f : Perm α) [
DecidableRel f.SameCycle] (n : Nat) (x : α) : cycleOf f ((f ^ n) x) = cycleOf f 
x
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.getElem_toList`：getElem_toList (n : Nat) (hn : n < length (to
List p x)) : (toList p x)[n] = (p ^ n) x
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `List.getElem_rotate`：getElem_rotate (l : List α) (n : Nat) (k : Nat) (h 
: k < (l.rotate n).length) : (l.rotate n)[k] = l[(k + n) % l.length]'(mod_lt _ (
length_ro…
· 使用定理 `Equiv.Perm.pow_mod_card_support_cycleOf_self_apply`：pow_mod_card_support
_cycleOf_self_apply [DecidableEq α] [Fintype α] (f : Perm α) (n : Nat) (x : α) :
 (f ^ (n % #(f.cycleOf x).support)) x = …
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
-/
theorem toList_pow_apply_eq_rotate (p : Perm α) (x : α) (k : ℕ) :
    p.toList ((p ^ k) x) = (p.toList x).rotate k := by
  apply ext_getElem
  · simp only [length_toList, cycleOf_self_apply_pow, length_rotate]
  · intro n hn hn'
    rw [getElem_toList, getElem_rotate, getElem_toList, length_toList,
      pow_mod_card_support_cycleOf_self_apply, pow_add, mul_apply]
/-
**Equiv.Perm.SameCycle.toList_isRotated** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Sa
meCycle`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {f : Equiv.Pe
rm α} {x y : α},   f.SameCycle x y → f.toList x ~r f.toList y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.exists_pow_eq_of_mem_support`：∀ {α : Type u_2} {x y
 : α} {f : Equiv.Perm α} [inst : DecidableEq α] [inst_1 : Fintype α],   f.SameCy
cle x y → x ∈ f.support → ∃ i < (f.cycl…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.toList_pow_apply_eq_rotate`：toList_pow_apply_eq_rotate (p : P
erm α) (x : α) (k : Nat) : p.toList ((p ^ k) x) = (p.toList x).rotate k
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.toList_eq_nil_iff`：toList_eq_nil_iff {p : Perm α} {x} : toLis
t p x = [] ↔ x ∉ p.support
· 使用定理 `List.isRotated_nil_iff'`：isRotated_nil_iff' : [] ~r l ↔ [] = l
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Equiv.Perm.SameCycle.mem_support_iff`：∀ {α : Type u_2} {x y : α} {f : Eq
uiv.Perm α} [inst : DecidableEq α] [inst_1 : Fintype α],   f.SameCycle x y → (x 
∈ f.support ↔ y ∈ f.suppor…
-/
theorem SameCycle.toList_isRotated {f : Perm α} {x y : α} (h : SameCycle f x y) :
    toList f x ~r toList f y := by
  by_cases hx : x ∈ f.support
  · obtain ⟨_ | k, _, hy⟩ := h.exists_pow_eq_of_mem_support hx
    · simp only [coe_one, id, pow_zero] at hy
      -- Porting note: added `IsRotated.refl`
      simp [hy, IsRotated.refl]
    use k.succ
    rw [← toList_pow_apply_eq_rotate, hy]
  · rw [toList_eq_nil_iff.mpr hx, isRotated_nil_iff', eq_comm, toList_eq_nil_iff]
    rwa [← h.mem_support_iff]
/-
**Equiv.Perm.pow_apply_mem_toList_iff_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `Equ
iv.Perm`。
形式化陈述：pow_apply_mem_toList_iff_mem_support {n : Nat} : (p ^ n) x in p.toList x ↔
 x in p.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_toList_iff`：mem_toList_iff {y : α} : y in toList p x ↔ Sa
meCycle p x y ∧ x in p.support
· 使用定理 `and_iff_right_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ b) ↔ b → a
· 使用定理 `Equiv.Perm.SameCycle.symm`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α}
, f.SameCycle x y → f.SameCycle y x
· 使用定理 `Equiv.Perm.sameCycle_pow_left`：sameCycle_pow_left {n : Nat} : SameCycle 
f ((f ^ n) x) y ↔ SameCycle f x y
· 使用定理 `Equiv.Perm.SameCycle.refl`：∀ {α : Type u_2} (f : Equiv.Perm α) (x : α), 
f.SameCycle x x
-/
theorem pow_apply_mem_toList_iff_mem_support {n : ℕ} : (p ^ n) x ∈ p.toList x ↔ x ∈ p.support := by
  rw [mem_toList_iff, and_iff_right_iff_imp]
  refine fun _ => SameCycle.symm ?_
  rw [sameCycle_pow_left]
/-
**Equiv.Perm.toList_formPerm_nil** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：toList_formPerm_nil (x : α) : toList (formPerm ([] : List α)) x = []
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.toList_one`：toList_one : toList (1 : Perm α) x = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toList_formPerm_nil (x : α) : toList (formPerm ([] : List α)) x = [] := by simp
/-
**Equiv.Perm.toList_formPerm_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：toList_formPerm_singleton (x y : α) : toList (formPerm [x]) y = []
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.toList_one`：toList_one : toList (1 : Perm α) x = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toList_formPerm_singleton (x y : α) : toList (formPerm [x]) y = [] := by simp
/-
**Equiv.Perm.toList_formPerm_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：toList_formPerm_nontrivial (l : List α) (hl : 2 <= l.length) (hn : Nodup l
) : toList (formPerm l) (l.get ⟨0, (zero_lt_two.trans_le hl)⟩) = l
参数：l : List α；hl : 2 <= l.length；hn : Nodup l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.isCycle_formPerm`：isCycle_formPerm (hl : Nodup l) (hn : 2 <= l.leng
th) : IsCycle (formPerm l)
· 使用定理 `List.support_formPerm_of_nodup`：support_formPerm_of_nodup [Fintype α] (l
 : List α) (h : Nodup l) (h' : forall x : α, l != [x]) : support (formPerm l) = 
l.toFinset
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Equiv.Perm.toList.eq_1`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : De
cidableEq α] (p : Equiv.Perm α) (x : α),   p.toList x = List.iterate (⇑p) x (p.c
ycleOf x).su…
· 使用定理 `Equiv.Perm.IsCycle.cycleOf_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {x : 
α} [inst : DecidableRel f.SameCycle], f.IsCycle → f x ≠ x → f.cycleOf x = f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.card_toFinset`：List.card_toFinset : #l.toFinset = l.dedup.length
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.dedup_eq_self`：dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l
· 使用定理 `List.ext_getElem`：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁
.length l₂.length, l₁[n]? = l₂[n]?) : l₁ = l₂
· 使用定理 `List.length_iterate`：length_iterate (f : α -> α) (a : α) (n : Nat) : len
gth (iterate f a n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `List.getElem_iterate`：getElem_iterate (f : α -> α) (a : α) (n : Nat) (i 
: Nat) (h : i < (iterate f a n).length) : (iterate f a n)[i] = f^[i] a
· 使用定理 `List.formPerm_pow_apply_getElem`：formPerm_pow_apply_getElem (l : List α)
 (w : Nodup l) (n : Nat) (i : Nat) (h : i < l.length) : (formPerm l ^ n) l[i] = 
l[(i + n) % l.length]…
（共 31 条，此处仅展示前 30 条）
-/
theorem toList_formPerm_nontrivial (l : List α) (hl : 2 ≤ l.length) (hn : Nodup l) :
    toList (formPerm l) (l.get ⟨0, (zero_lt_two.trans_le hl)⟩) = l := by
  have hc : l.formPerm.IsCycle := List.isCycle_formPerm hn hl
  have hs : l.formPerm.support = l.toFinset := by
    refine support_formPerm_of_nodup _ hn ?_
    rintro _ rfl
    simp at hl
  rw [toList, hc.cycleOf_eq (mem_support.mp _), hs, card_toFinset, dedup_eq_self.mpr hn]
  · refine ext_getElem (by simp) fun k hk hk' => ?_
    simp only [get_eq_getElem, getElem_iterate, iterate_eq_pow, formPerm_pow_apply_getElem _ hn,
      zero_add, Nat.mod_eq_of_lt hk']
  · simp [hs]
/-
**Equiv.Perm.toList_formPerm_isRotated_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
形式化陈述：toList_formPerm_isRotated_self (l : List α) (hl : 2 <= l.length) (hn : Nod
up l) (x : α) (hx : x in l) : toList (formPerm l) x ~r l
参数：l : List α；hl : 2 <= l.length；hn : Nodup l；x : α；hx : x in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.get_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ n, l.g
et n = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.formPerm_eq_of_isRotated`：formPerm_eq_of_isRotated {l l' : List α} 
(hd : Nodup l) (h : l ~r l') : formPerm l = formPerm l'
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `List.get_eq_get_rotate`：get_eq_get_rotate (l : List α) (n : Nat) (k : Fi
n l.length) : l.get k = (l.rotate n).get ⟨(l.length - n % l.length + k) % l.leng
th, (Nat.mod…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Equiv.Perm.toList_formPerm_nontrivial`：toList_formPerm_nontrivial (l : L
ist α) (hl : 2 <= l.length) (hn : Nodup l) : toList (formPerm l) (l.get ⟨0, (zer
o_lt_two.trans_le hl)⟩) = l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem toList_formPerm_isRotated_self (l : List α) (hl : 2 ≤ l.length) (hn : Nodup l) (x : α)
    (hx : x ∈ l) : toList (formPerm l) x ~r l := by
  obtain ⟨k, hk, rfl⟩ := get_of_mem hx
  have hr : l ~r l.rotate k := ⟨k, rfl⟩
  rw [formPerm_eq_of_isRotated hn hr]
  rw [get_eq_get_rotate l k k]
  simp only [Nat.mod_eq_of_lt k.2, tsub_add_cancel_of_le (le_of_lt k.2), Nat.mod_self]
  rw [toList_formPerm_nontrivial]
  · simp
  · simpa using hl
  · simpa using hn
/-
**Equiv.Perm.formPerm_toList** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：formPerm_toList (f : Perm α) (x : α) : formPerm (toList f x) = f.cycleOf x
参数：f : Perm α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.cycleOf_eq_one_iff`：cycleOf_eq_one_iff (f : Perm α) [Decidabl
eRel f.SameCycle] : cycleOf f x = 1 ↔ f x = x
· 使用定理 `Equiv.Perm.toList_eq_nil_iff`：toList_eq_nil_iff {p : Perm α} {x} : toLis
t p x = [] ↔ x ∉ p.support
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `List.formPerm_nil`：formPerm_nil : formPerm ([] : List α) = 1
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.Perm.SameCycle.exists_pow_eq_of_mem_support`：∀ {α : Type u_2} {x y
 : α} {f : Equiv.Perm α} [inst : DecidableEq α] [inst_1 : Fintype α],   f.SameCy
cle x y → x ∈ f.support → ∃ i < (f.cycl…
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.cycleOf_apply_apply_pow_self`：cycleOf_apply_apply_pow_self (f
 : Perm α) [DecidableRel f.SameCycle] (x : α) (k : Nat) : cycleOf f x ((f ^ k) x
) = (f ^ (k + 1) : Perm α) x
· 使用定理 `Equiv.Perm.mem_toList_iff`：mem_toList_iff {y : α} : y in toList p x ↔ Sa
meCycle p x y ∧ x in p.support
· 使用定理 `List.formPerm_apply_mem_eq_next`：formPerm_apply_mem_eq_next (hl : Nodup 
l) (x : α) (hx : x in l) : formPerm l x = next l x hx
· 使用定理 `Equiv.Perm.nodup_toList`：nodup_toList (p : Perm α) (x : α) : Nodup (toLi
st p x)
· 使用定理 `Equiv.Perm.next_toList_eq_apply`：next_toList_eq_apply (p : Perm α) (x y 
: α) (hy : y in toList p x) : next (toList p x) y hy = p y
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Equiv.Perm.cycleOf_apply_of_not_sameCycle`：cycleOf_apply_of_not_sameCycl
e [DecidableRel f.SameCycle] : ¬SameCycle f x y -> cycleOf f x y = y
· 使用定理 `List.formPerm_apply_of_notMem`：formPerm_apply_of_notMem (h : x ∉ l) : fo
rmPerm l x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem formPerm_toList (f : Perm α) (x : α) : formPerm (toList f x) = f.cycleOf x := by
  by_cases hx : f x = x
  · rw [(cycleOf_eq_one_iff f).mpr hx, toList_eq_nil_iff.mpr (notMem_support.mpr hx),
      formPerm_nil]
  ext y
  by_cases hy : SameCycle f x y
  · obtain ⟨k, _, rfl⟩ := hy.exists_pow_eq_of_mem_support (mem_support.mpr hx)
    rw [cycleOf_apply_apply_pow_self, List.formPerm_apply_mem_eq_next (nodup_toList f x),
      next_toList_eq_apply, pow_succ', mul_apply]
    rw [mem_toList_iff]
    exact ⟨⟨k, rfl⟩, mem_support.mpr hx⟩
  · rw [cycleOf_apply_of_not_sameCycle hy, formPerm_apply_of_notMem]
    simp [mem_toList_iff, hy]

/-- Given a cyclic `f : Perm α`, generate the `Cycle α` in the order
of application of `f`. Implemented by finding an element `x : α`
in the support of `f` in `Finset.univ`, and iterating on using
`Equiv.Perm.toList f x`.
-/
/-
**Equiv.Perm.toCycle** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：toCycle (f : Perm α) (hf : IsCycle f) : Cycle α
参数：f : Perm α；hf : IsCycle f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cyclic `f : Perm α`, generate the `Cycle α` in the order
of application of `f`. Implemented by finding an element `x : α`
in the support of `f` in `Finset.univ`, and iterating on using
`Equiv.Perm.toList f x`.
-/
def toCycle (f : Perm α) (hf : IsCycle f) : Cycle α :=
  Multiset.recOn (Finset.univ : Finset α).val (Quot.mk _ [])
    (fun x _ l => if f x = x then l else toList f x)
    (by
      intro x y _ s
      refine heq_of_eq ?_
      split_ifs with hx hy hy <;> try rfl
      have hc : SameCycle f x y := IsCycle.sameCycle hf hx hy
      exact Quotient.sound' hc.toList_isRotated)

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.Perm.toCycle_eq_toList** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：toCycle_eq_toList (f : Perm α) (hf : IsCycle f) (x : α) (hx : f x != x) : 
toCycle f hf = toList f x
参数：f : Perm α；hf : IsCycle f；x : α；hx : f x != x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.toCycle.eq_1`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : D
ecidableEq α] (f : Equiv.Perm α) (hf : f.IsCycle),   f.toCycle hf =     Finset.u
niv.val.recOn…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.recOn_cons`：recOn_cons (a : α) (m : Multiset α) : (a ::ₘ m).rec
On C_0 C_cons C_cons_heq = C_cons a m (m.recOn C_0 C_cons C_cons_heq)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem toCycle_eq_toList (f : Perm α) (hf : IsCycle f) (x : α) (hx : f x ≠ x) :
    toCycle f hf = toList f x := by
  have key : (Finset.univ : Finset α).val = x ::ₘ Finset.univ.val.erase x := by simp
  rw [toCycle, key]
  simp [hx]
/-
**Equiv.Perm.exists_toCycle_toList** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：exists_toCycle_toList (f : Perm α) (hf : IsCycle f) : exists x, toCycle f 
hf = toList f x
参数：f : Perm α；hf : IsCycle f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.toCycle_eq_toList`：toCycle_eq_toList (f : Perm α) (hf : IsCyc
le f) (x : α) (hx : f x != x) : toCycle f hf = toList f x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem exists_toCycle_toList (f : Perm α) (hf : IsCycle f) : ∃ x, toCycle f hf = toList f x :=
  Exists.casesOn hf (fun x h => ⟨x, Perm.toCycle_eq_toList f hf x h.1⟩)
/-
**Equiv.Perm.nodup_toCycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：nodup_toCycle (f : Perm α) (hf : IsCycle f) : (toCycle f hf).Nodup
参数：f : Perm α；hf : IsCycle f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.toCycle_eq_toList`：toCycle_eq_toList (f : Perm α) (hf : IsCyc
le f) (x : α) (hx : f x != x) : toCycle f hf = toList f x
· 使用定理 `Equiv.Perm.nodup_toList`：nodup_toList (p : Perm α) (x : α) : Nodup (toLi
st p x)
-/
theorem nodup_toCycle (f : Perm α) (hf : IsCycle f) : (toCycle f hf).Nodup := by
  obtain ⟨x, hx, -⟩ := id hf
  simpa [toCycle_eq_toList f hf x hx] using nodup_toList _ _
/-
**Equiv.Perm.nontrivial_toCycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：nontrivial_toCycle (f : Perm α) (hf : IsCycle f) : (toCycle f hf).Nontrivi
al
参数：f : Perm α；hf : IsCycle f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.toCycle_eq_toList`：toCycle_eq_toList (f : Perm α) (hf : IsCyc
le f) (x : α) (hx : f x != x) : toCycle f hf = toList f x
· 使用定理 `Cycle.nontrivial_coe_nodup_iff`：nontrivial_coe_nodup_iff {l : List α} (h
l : l.Nodup) : Nontrivial (l : Cycle α) ↔ 2 <= l.length
· 使用定理 `Equiv.Perm.nodup_toList`：nodup_toList (p : Perm α) (x : α) : Nodup (toLi
st p x)
· 使用定理 `Equiv.Perm.length_toList`：length_toList : length (toList p x) = (cycleOf
 p x).support.card
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem nontrivial_toCycle (f : Perm α) (hf : IsCycle f) : (toCycle f hf).Nontrivial := by
  obtain ⟨x, hx, -⟩ := id hf
  simp [toCycle_eq_toList f hf x hx, hx, Cycle.nontrivial_coe_nodup_iff (nodup_toList _ _)]

@[simp]
/-
**Equiv.Perm.mem_toCycle_iff_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_toCycle_iff_support (f : Perm α) (hf : f.IsCycle) : x in f.toCycle hf 
↔ f x != x
参数：f : Perm α；hf : f.IsCycle。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.exists_toCycle_toList`：exists_toCycle_toList (f : Perm α) (hf
 : IsCycle f) : exists x, toCycle f hf = toList f x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_toList_iff`：mem_toList_iff {y : α} : y in toList p x ↔ Sa
meCycle p x y ∧ x in p.support
· 使用定理 `Equiv.Perm.isCycle_iff_sameCycle`：isCycle_iff_sameCycle (hx : f x != x) 
: IsCycle f ↔ forall {y}, SameCycle f x y ↔ f y != y
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.toCycle_eq_toList`：toCycle_eq_toList (f : Perm α) (hf : IsCyc
le f) (x : α) (hx : f x != x) : toCycle f hf = toList f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_toCycle_iff_support (f : Perm α) (hf : f.IsCycle) : x ∈ f.toCycle hf ↔ f x ≠ x := by
  constructor
  · have ⟨l, hl⟩ := exists_toCycle_toList f hf
    simp only [hl, Cycle.mem_coe_iff, ne_eq]
    intro h
    have ⟨h1, h2⟩ := mem_toList_iff.mp h
    exact ((isCycle_iff_sameCycle (mem_support.mp h2)).mp (y := x) hf).mp h1
  · intro h
    simp only [toCycle_eq_toList f hf x h, Cycle.mem_coe_iff, toList, mem_iterate, iterate_eq_pow]
    use 0
    exact ⟨by simpa, by simp⟩

@[simp]
/-
**Equiv.Perm.toCycle_next** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：toCycle_next (f : Perm α) (hf : f.IsCycle) (hx : x in toCycle f hf) : (toC
ycle f hf).next (nodup_toCycle f hf) x hx = f x
参数：f : Perm α；hf : f.IsCycle；hx : x in toCycle f hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.nodup_toCycle`：nodup_toCycle (f : Perm α) (hf : IsCycle f) : 
(toCycle f hf).Nodup
· 使用定理 `Equiv.Perm.exists_toCycle_toList`：exists_toCycle_toList (f : Perm α) (hf
 : IsCycle f) : exists x, toCycle f hf = toList f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cycle.next.congr_simp`：∀ {α : Type u_1} [inst : DecidableEq α] (s s_1 : 
Cycle α) (e_s : s = s_1) (_hs : s.Nodup) (x x_1 : α) (e_x : x = x_1)   (_hx : x 
∈ s), s.nex…
· 使用定理 `Equiv.Perm.next_toList_eq_apply`：next_toList_eq_apply (p : Perm α) (x y 
: α) (hy : y in toList p x) : next (toList p x) y hy = p y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem toCycle_next (f : Perm α) (hf : f.IsCycle) (hx : x ∈ toCycle f hf) :
    (toCycle f hf).next (nodup_toCycle f hf) x hx = f x := by
  have ⟨l, hl⟩ := exists_toCycle_toList f hf
  simp only [hl, Cycle.mem_coe_iff] at ⊢ hx
  exact Equiv.Perm.next_toList_eq_apply f l x hx

set_option backward.isDefEq.respectTransparency false in
/-- Any cyclic `f : Perm α` is isomorphic to the nontrivial `Cycle α`
that corresponds to repeated application of `f`.
The forward direction is implemented by `Equiv.Perm.toCycle`.
-/
/-
**Equiv.Perm.isoCycle** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：isoCycle : { f : Perm α // IsCycle f } ≃ { s : Cycle α // s.Nodup ∧ s.Nont
rivial } where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any cyclic `f : Perm α` is isomorphic to the nontrivial `Cycle α`
that corresponds to repeated application of `f`.
The forward direction is implemented by `Equiv.Perm.toCycle`.
-/
def isoCycle : { f : Perm α // IsCycle f } ≃ { s : Cycle α // s.Nodup ∧ s.Nontrivial } where
  toFun f := ⟨toCycle (f : Perm α) f.prop, nodup_toCycle (f : Perm α) f.prop,
    nontrivial_toCycle _ f.prop⟩
  invFun s := ⟨(s : Cycle α).formPerm s.prop.left, (s : Cycle α).isCycle_formPerm _ s.prop.right⟩
  left_inv f := by
    obtain ⟨x, hx, -⟩ := id f.prop
    simpa [toCycle_eq_toList (f : Perm α) f.prop x hx, formPerm_toList, Subtype.ext_iff] using
      f.prop.cycleOf_eq hx
  right_inv s := by
    rcases s with ⟨⟨s⟩, hn, ht⟩
    obtain ⟨x, -, -, hx, -⟩ := id ht
    have hl : 2 ≤ s.length := by simpa using Cycle.length_nontrivial ht
    simp only [Cycle.mk_eq_coe, Cycle.nodup_coe_iff, Cycle.mem_coe_iff,
      Cycle.formPerm_coe] at hn hx ⊢
    apply Subtype.ext
    dsimp
    rw [toCycle_eq_toList _ _ x]
    · refine Quotient.sound' ?_
      exact toList_formPerm_isRotated_self _ hl hn _ hx
    · rw [← mem_support, support_formPerm_of_nodup _ hn]
      · simpa using hx
      · rintro _ rfl
        simp at hl

end Fintype

section Finite

variable [Finite α] [DecidableEq α]

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.Perm.IsCycle.existsUnique_cycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Is
Cycle`。
形式化陈述：∀ {α : Type u_1} [Finite α] [inst : DecidableEq α] {f : Equiv.Perm α},   f
.IsCycle → ∃! s, ∃ (h : s.Nodup), s.formPerm h = f
参数：h : s.Nodup。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.Perm.nodup_toList`：nodup_toList (p : Perm α) (x : α) : Nodup (toLi
st p x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.formPerm_toList`：formPerm_toList (f : Perm α) (x : α) : formP
erm (toList f x) = f.cycleOf x
· 使用定理 `Equiv.Perm.IsCycle.cycleOf_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {x : 
α} [inst : DecidableRel f.SameCycle], f.IsCycle → f x ≠ x → f.cycleOf x = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.IsRotated.symm`：∀ {α : Type u} {l l' : List α}, l ~r l' → l' ~r l
· 使用定理 `Equiv.Perm.toList_formPerm_isRotated_self`：toList_formPerm_isRotated_sel
f (l : List α) (hl : 2 <= l.length) (hn : Nodup l) (x : α) (hx : x in l) : toLis
t (formPerm l) x ~r l
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.formPerm_eq_one_iff`：formPerm_eq_one_iff (hl : Nodup l) : formPerm 
l = 1 ↔ l.length <= 1
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
· 使用定理 `List.support_formPerm_le`：support_formPerm_le [Fintype α] : support (for
mPerm l) <= l.toFinset
-/
theorem IsCycle.existsUnique_cycle {f : Perm α} (hf : IsCycle f) :
    ∃! s : Cycle α, ∃ h : s.Nodup, s.formPerm h = f := by
  cases nonempty_fintype α
  obtain ⟨x, hx, hy⟩ := id hf
  refine ⟨f.toList x, ⟨nodup_toList f x, ?_⟩, ?_⟩
  · simp [formPerm_toList, hf.cycleOf_eq hx]
  · rintro ⟨l⟩ ⟨hn, rfl⟩
    simp only [Cycle.mk_eq_coe, Cycle.coe_eq_coe, Cycle.formPerm_coe]
    refine (toList_formPerm_isRotated_self _ ?_ hn _ ?_).symm
    · contrapose! hx
      suffices formPerm l = 1 by simp [this]
      rw [formPerm_eq_one_iff _ hn]
      exact Nat.le_of_lt_succ hx
    · rw [← mem_toFinset]
      refine support_formPerm_le l ?_
      simpa using hx
/-
**Equiv.Perm.IsCycle.existsUnique_cycle_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Equiv
.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_1} [Finite α] [inst : DecidableEq α] {f : Equiv.Perm α}, f.I
sCycle → ∃! s, (↑s).formPerm ⋯ = f
参数：↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Equiv.Perm.IsCycle.existsUnique_cycle`：∀ {α : Type u_1} [Finite α] [inst
 : DecidableEq α] {f : Equiv.Perm α},   f.IsCycle → ∃! s, ∃ (h : s.Nodup), s.for
mPerm h = f
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
-/
theorem IsCycle.existsUnique_cycle_subtype {f : Perm α} (hf : IsCycle f) :
    ∃! s : { s : Cycle α // s.Nodup }, (s : Cycle α).formPerm s.prop = f := by
  obtain ⟨s, ⟨hs, rfl⟩, hs'⟩ := hf.existsUnique_cycle
  refine ⟨⟨s, hs⟩, rfl, ?_⟩
  rintro ⟨t, ht⟩ ht'
  simpa using hs' _ ⟨ht, ht'⟩
/-
**Equiv.Perm.IsCycle.existsUnique_cycle_nontrivial_subtype** 是 Mathlib 中的一个定理，位于
命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_1} [Finite α] [inst : DecidableEq α] {f : Equiv.Perm α}, f.I
sCycle → ∃! s, (↑s).formPerm ⋯ = f
参数：↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.Perm.IsCycle.existsUnique_cycle_subtype`：∀ {α : Type u_1} [Finite 
α] [inst : DecidableEq α] {f : Equiv.Perm α}, f.IsCycle → ∃! s, (↑s).formPerm ⋯ 
= f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cycle.Nodup.nontrivial_iff`：∀ {α : Type u_1} {s : Cycle α}, s.Nodup → (s
.Nontrivial ↔ ¬s.Subsingleton)
· 使用定理 `Equiv.Perm.IsCycle.ne_one`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycl
e → f ≠ 1
· 使用定理 `Cycle.formPerm_subsingleton`：formPerm_subsingleton (s : Cycle α) (h : Su
bsingleton s) : formPerm s h.nodup = 1
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
-/
theorem IsCycle.existsUnique_cycle_nontrivial_subtype {f : Perm α} (hf : IsCycle f) :
    ∃! s : { s : Cycle α // s.Nodup ∧ s.Nontrivial }, (s : Cycle α).formPerm s.prop.left = f := by
  obtain ⟨⟨s, hn⟩, hs, hs'⟩ := hf.existsUnique_cycle_subtype
  refine ⟨⟨s, hn, ?_⟩, ?_, ?_⟩
  · rw [hn.nontrivial_iff]
    subst f
    intro H
    refine hf.ne_one ?_
    simpa using Cycle.formPerm_subsingleton _ H
  · simpa using hs
  · rintro ⟨t, ht, ht'⟩ ht''
    simpa using hs' ⟨t, ht⟩ ht''

end Finite

variable [Fintype α] [DecidableEq α]

/-- Any cyclic `f : Perm α` is isomorphic to the nontrivial `Cycle α`
that corresponds to repeated application of `f`.
The forward direction is implemented by finding this `Cycle α` using `Fintype.choose`.
-/
/-
**Equiv.Perm.isoCycle'** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：isoCycle' : { f : Perm α // IsCycle f } ≃ { s : Cycle α // s.Nodup ∧ s.Non
trivial }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any cyclic `f : Perm α` is isomorphic to the nontrivial `Cycle α`
that corresponds to repeated application of `f`.
The forward direction is implemented by finding this `Cycle α` using `Fintype.ch
oose`.
-/
def isoCycle' : { f : Perm α // IsCycle f } ≃ { s : Cycle α // s.Nodup ∧ s.Nontrivial } :=
  let f : { s : Cycle α // s.Nodup ∧ s.Nontrivial } → { f : Perm α // IsCycle f } :=
    fun s => ⟨(s : Cycle α).formPerm s.prop.left, (s : Cycle α).isCycle_formPerm _ s.prop.right⟩
  { toFun := Fintype.bijInv (show Function.Bijective f by
      rw [Function.bijective_iff_existsUnique]
      rintro ⟨f, hf⟩
      simp only [Subtype.ext_iff]
      exact hf.existsUnique_cycle_nontrivial_subtype)
    invFun := f
    left_inv := Fintype.rightInverse_bijInv _
    right_inv := Fintype.leftInverse_bijInv _ }

-- mutes `'decide' tactic does nothing [linter.unusedTactic]`
set_option linter.unusedTactic false in
@[inherit_doc Cycle.formPerm]
notation3 (prettyPrint := false) "c[" (l", "* => foldr (h t => List.cons h t) List.nil) "]" =>
  Cycle.formPerm (Cycle.ofList l) (Iff.mpr Cycle.nodup_coe_iff (by decide))

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Represents a permutation as product of disjoint cycles:
```
#eval (c[0, 1, 2, 3] : Perm (Fin 4))
-- c[0, 1, 2, 3]

#eval (c[3, 1] * c[0, 2] : Perm (Fin 4))
-- c[0, 2] * c[1, 3]

#eval (c[1, 2, 3] * c[0, 1, 2] : Perm (Fin 4))
-- c[0, 2] * c[1, 3]

#eval (c[1, 2, 3] * c[0, 1, 2] * c[3, 1] * c[0, 2] : Perm (Fin 4))
-- 1
```
-/
/-
**Equiv.Perm.instRepr** 是 Mathlib 中的一个unsafe-def，位于命名空间 `Equiv.Perm`。
形式化陈述：{α : Type u_1} → [Fintype α] → [DecidableEq α] → [Repr α] → Repr (Equiv.Pe
rm α)
参数：Equiv.Perm α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Represents a permutation as product of disjoint cycles:
```
#eval (c[0, 1, 2, 3] : Perm (Fin 4))
-- c[0, 1, 2, 3]

#eval (c[3, 1] * c[0, 2] : Perm (Fin 4))
-- c[0, 2] * c[1, 3]

#eval (c[1, 2, 3] * c[0, 1, 2] : Perm (Fin 4))
-- c[0, 2] * c[1, 3]

#eval (c[1, 2, 3] * c[0, 1, 2] * c[3, 1] * c[0, 2] : Perm (Fin 4))
-- 1
```
-/
unsafe instance instRepr [Repr α] : Repr (Perm α) where
  reprPrec f prec :=
    -- Obtain a list of formats which represents disjoint cycles.
    letI l := Quot.unquot <| Multiset.map repr <| Multiset.pmap toCycle
      (Perm.cycleFactorsFinset f).val
      fun _ hg => (mem_cycleFactorsFinset_iff.mp (Finset.mem_def.mpr hg)).left
    -- And intercalate `*`s.
    match l with
    | []  => "1"
    | [f] => f
    | l   =>
      -- multiple terms, use `*` precedence
      (if prec ≥ 70 then Lean.Format.paren else id)
      (Lean.Format.fill
        (Lean.Format.joinSep l (" *" ++ Lean.Format.line)))

end Equiv.Perm

