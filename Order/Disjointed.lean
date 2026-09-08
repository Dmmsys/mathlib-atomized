/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies, David Loeffler
-/
module

public import Mathlib.Order.PartialSups
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.SuccPred.LinearLocallyFinite
public import Mathlib.Order.Interval.Finset.SuccPred

/-!
# Making a sequence disjoint

This file defines the way to make a sequence of sets - or, more generally, a map from a partially
ordered type `ι` into a (generalized) Boolean algebra `α` - into a *pairwise disjoint* sequence with
the same partial sups.

For a sequence `f : ℕ → α`, this new sequence will be `f 0`, `f 1 \ f 0`, `f 2 \ (f 0 ⊔ f 1) ⋯`.
It is actually unique, as `disjointed_unique` shows.

## Main declarations

* `disjointed f`: The map sending `i` to `f i \ (⨆ j < i, f j)`. We require the index type to be a
  `LocallyFiniteOrderBot` to ensure that the supremum is well defined.
* `partialSups_disjointed`: `disjointed f` has the same partial sups as `f`.
* `disjoint_disjointed`: The elements of `disjointed f` are pairwise disjoint.
* `disjointed_unique`: `disjointed f` is the only pairwise disjoint sequence having the same partial
  sups as `f`.
* `Fintype.sup_disjointed` (for finite `ι`) or `iSup_disjointed` (for complete `α`):
  `disjointed f` has the same supremum as `f`. Limiting case of `partialSups_disjointed`.
* `Fintype.exists_disjointed_le`: for any finite family `f : ι → α`, there exists a pairwise
  disjoint family `g : ι → α` which is bounded above by `f` and has the same supremum. This is
  an analogue of `disjointed` for arbitrary finite index types (but without any uniqueness).

We also provide set notation variants of some lemmas.
-/

@[expose] public section

assert_not_exists SuccAddOrder

open Finset Order

variable {α ι : Type*}

open scoped Function -- required for scoped `on` notation

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α]

section Preorder -- the *index type* is a preorder

variable [Preorder ι] [LocallyFiniteOrderBot ι]

/-- The function mapping `i` to `f i \ (⨆ j < i, f j)`. When `ι` is a partial order, this is the
unique function `g` having the same `partialSups` as `f` and such that `g i` and `g j` are
disjoint whenever `i < j`. -/
/-
**disjointed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：disjointed (f : ι -> α) (i : ι) : α
参数：f : ι -> α；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function mapping `i` to `f i \ (⨆ j < i, f j)`. When `ι` is a partial order,
 this is the
unique function `g` having the same `partialSups` as `f` and such that `g i` and
 `g j` are
disjoint whenever `i < j`.
-/
def disjointed (f : ι → α) (i : ι) : α := f i \ (Iio i).sup f
/-
**disjointed_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjointed_apply (f : ι -> α) (i : ι) : disjointed f i = f i \ (Iio i).sup
 f
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma disjointed_apply (f : ι → α) (i : ι) : disjointed f i = f i \ (Iio i).sup f := rfl
/-
**disjointed_of_isMin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjointed_of_isMin (f : ι -> α) {i : ι} (hn : IsMin i) : disjointed f i =
 f i
参数：f : ι -> α；hn : IsMin i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_eq_empty`：coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s =
 ∅
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Set.Iio_eq_empty_iff`：Iio_eq_empty_iff : Iio a = ∅ ↔ IsMin a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `sdiff_bot`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, a \ ⊥ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma disjointed_of_isMin (f : ι → α) {i : ι} (hn : IsMin i) :
    disjointed f i = f i := by
  have : Iio i = ∅ := by rwa [← Finset.coe_eq_empty, coe_Iio, Set.Iio_eq_empty_iff]
  simp only [disjointed_apply, this, sup_empty, sdiff_bot]
/-
**disjointed_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : GeneralizedBooleanAlgebra α] [inst
_1 : Preorder ι]   [inst_2 : LocallyFiniteOrderBot ι] [inst_3 : OrderBot ι] (f :
 ι → α), disjointed f ⊥ = f ⊥
参数：f : ι → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `disjointed_of_isMin`：disjointed_of_isMin (f : ι -> α) {i : ι} (hn : IsMi
n i) : disjointed f i = f i
· 使用定理 `isMin_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α], IsM
in ⊥
-/
@[simp] lemma disjointed_bot [OrderBot ι] (f : ι → α) : disjointed f ⊥ = f ⊥ :=
  disjointed_of_isMin _ isMin_bot
/-
**disjointed_le_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjointed_le_id : disjointed <= (id : (ι -> α) -> ι -> α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem disjointed_le_id : disjointed ≤ (id : (ι → α) → ι → α) :=
  fun _ _ ↦ sdiff_le
/-
**disjointed_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjointed_le (f : ι -> α) : disjointed f <= f
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjointed_le_id`：disjointed_le_id : disjointed <= (id : (ι -> α) -> ι -
> α)
-/
theorem disjointed_le (f : ι → α) : disjointed f ≤ f :=
  disjointed_le_id f
/-
**disjoint_disjointed_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_disjointed_of_lt (f : ι -> α) {i j : ι} (h : i < j) : Disjoint (d
isjointed f i) (disjointed f j)
参数：f : ι -> α；h : i < j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `disjointed_le`：disjointed_le (f : ι -> α) : disjointed f <= f
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iio a ↔ x < a
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
-/
theorem disjoint_disjointed_of_lt (f : ι → α) {i j : ι} (h : i < j) :
    Disjoint (disjointed f i) (disjointed f j) :=
  (disjoint_sdiff_self_right.mono_left <| le_sup (mem_Iio.mpr h)).mono_left (disjointed_le f i)
/-
**disjointed_eq_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjointed_eq_self {f : ι -> α} {i : ι} (hf : forall j < i, Disjoint (f j)
 (f i)) : disjointed f i = f i
参数：hf : forall j < i, Disjoint (f j) (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `disjointed_apply`：disjointed_apply (f : ι -> α) (i : ι) : disjointed f i
 = f i \ (Iio i).sup f
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Finset.sup_inf_distrib_left`：sup_inf_distrib_left (s : Finset ι) (f : ι 
-> α) (a : α) : a ⊓ s.sup f = s.sup fun i => a ⊓ f i
· 使用定理 `Finset.sup_congr`：sup_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall 
a in s₂, f a = g a) : s₁.sup f = s₂.sup g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Finset.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iio a ↔ x < a
· 使用定理 `Finset.sup_bot`：sup_bot (s : Finset β) : (s.sup fun _ => ⊥) = (⊥ : α)
-/
lemma disjointed_eq_self {f : ι → α} {i : ι} (hf : ∀ j < i, Disjoint (f j) (f i)) :
    disjointed f i = f i := by
  rw [disjointed_apply, sdiff_eq_left, disjoint_iff, sup_inf_distrib_left,
    sup_congr rfl <| fun j hj ↦ disjoint_iff.mp <| (hf _ (mem_Iio.mp hj)).symm]
  exact sup_bot _

/- NB: The original statement for `ι = ℕ` was a `def` and worked for `p : α → Sort*`. I couldn't
prove the `Sort*` version for general `ι`, but all instances of `disjointedRec` in the library are
for Prop anyway. -/
/--
An induction principle for `disjointed`. To prove something about `disjointed f i`, it's
enough to prove it for `f i` and being able to extend through diffs.
-/
/-
**disjointedRec** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjointedRec {f : ι -> α} {p : α -> Prop} (hdiff : forall ⦃t i⦄, p t -> p
 (t \ f i)) : forall ⦃i⦄, p (f i) -> p (disjointed f i)
参数：hdiff : forall ⦃t i⦄, p t -> p (t \ f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjointed.eq_1`：∀ {α : Type u_1} {ι : Type u_2} [inst : GeneralizedBool
eanAlgebra α] [inst_1 : Preorder ι]   [inst_2 : LocallyFiniteOrderBot ι] (f : ι 
→ α) …
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `sdiff_bot`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, a \ ⊥ = a
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiff_sdiff`：sdiff_sdiff (a b c : α) : (a \ b) \ c = a \ (b ⊔ c)

--- 原说明 ---
An induction principle for `disjointed`. To prove something about `disjointed f 
i`, it's
enough to prove it for `f i` and being able to extend through diffs.
-/
lemma disjointedRec {f : ι → α} {p : α → Prop} (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i)) :
    ∀ ⦃i⦄, p (f i) → p (disjointed f i) := by
  classical
  intro i hpi
  rw [disjointed]
  suffices ∀ (s : Finset ι), p (f i \ s.sup f) from this _
  intro s
  induction s using Finset.induction with
  | empty => simpa only [sup_empty, sdiff_bot] using hpi
  | insert _ _ ht IH =>
    rw [sup_insert, sup_comm, ← sdiff_sdiff]
    exact hdiff IH

end Preorder

section PartialOrder -- the index type is a partial order

variable [PartialOrder ι] [LocallyFiniteOrderBot ι]

@[simp]
/-
**partialSups_disjointed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partialSups_disjointed (f : ι -> α) : partialSups (disjointed f) = partial
Sups f
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用定理 `Finset.notMem_Iio_self`：notMem_Iio_self {b : α} : b ∉ Iio b
· 使用定理 `Finset.Iic_eq_cons_Iio`：Iic_eq_cons_Iio (b : α) : Iic b = (Iio b).cons b
 notMem_Iio_self
· 使用定理 `Finset.cons.congr_simp`：∀ {α : Type u_1} (a a_1 : α) (e_a : a = a_1) (s 
s_1 : Finset α) (e_s : s = s_1) (h : a ∉ s),   Finset.cons a s h = Finset.cons a
_1 s_1 ⋯
· 使用定理 `Finset.sup'.congr_simp`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilatt
iceSup α] (s s_1 : Finset β) (e_s : s = s_1) (H : s.Nonempty)   (f f_1 : β → α),
 f = f_1 → s…
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `sdiff_bot`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, a \ ⊥ = a
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_biUnion`：sup_biUnion [DecidableEq β] (s : Finset γ) (t : γ ->
 Finset β) : (s.biUnion t).sup f = s.sup fun x => (t x).sup f
· 使用定理 `Finset.sup_congr`：sup_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall 
a in s₂, f a = g a) : s₁.sup f = s₂.sup g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 40 条，此处仅展示前 30 条）
-/
theorem partialSups_disjointed (f : ι → α) :
    partialSups (disjointed f) = partialSups f := by
  -- This seems to be much more awkward than the case of linear orders, because the supremum
  -- in the definition of `disjointed` can involve multiple "paths" through the poset.
  classical
  -- We argue by induction on the size of `Iio i`.
  suffices ∀ r i (hi : #(Iio i) ≤ r), partialSups (disjointed f) i = partialSups f i from
    OrderHom.ext _ _ (funext fun i ↦ this _ i le_rfl)
  intro r i hi
  induction r generalizing i with
  | zero =>
    -- Base case: `n` is minimal, so `partialSups f i = partialSups (disjointed f) n = f i`.
    simp only [Nat.le_zero, card_eq_zero] at hi
    simp only [partialSups_apply, Iic_eq_cons_Iio, hi, disjointed_apply, sup'_eq_sup, sup_cons,
      sup_empty, sdiff_bot]
  | succ n ih =>
    -- Induction step: first WLOG arrange that `#(Iio i) = r + 1`
    rcases lt_or_eq_of_le hi with hn | hn
    · exact ih _ <| Nat.le_of_lt_succ hn
    simp only [partialSups_apply (disjointed f), Iic_eq_cons_Iio, sup'_eq_sup, sup_cons]
    -- Key claim: we can write `Iio i` as a union of (finitely many) `Iic` intervals.
    have hun : (Iio i).biUnion Iic = Iio i := by
      ext r; simpa using ⟨fun ⟨a, ha⟩ ↦ ha.2.trans_lt ha.1, fun hr ↦ ⟨r, hr, le_rfl⟩⟩
    -- Use claim and `sup_biUnion` to rewrite the supremum in the definition of `disjointed f`
    -- in terms of suprema over `Iic`'s. Then the RHS is a `sup` over `partialSups`, which we
    -- can rewrite via the induction hypothesis.
    rw [← hun, sup_biUnion, sup_congr rfl (g := partialSups f)]
    · simp only [funext (partialSups_apply f), sup'_eq_sup, ← sup_biUnion, hun]
      simp only [disjointed, sdiff_sup_self, Iic_eq_cons_Iio, sup_cons]
    · simp only [partialSups, sup'_eq_sup, OrderHom.coe_mk] at ih ⊢
      refine fun x hx ↦ ih x ?_
      -- Remains to show `∀ x in Iio i, #(Iio x) ≤ r`.
      rw [← Nat.lt_add_one_iff, ← hn]
      apply lt_of_lt_of_le (b := #(Iic x))
      · simpa only [Iic_eq_cons_Iio, card_cons] using Nat.lt_succ_self _
      · refine card_le_card (fun r hr ↦ ?_)
        simp only [mem_Iic, mem_Iio] at hx hr ⊢
        exact hr.trans_lt hx
/-
**Fintype.sup_disjointed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fintype.sup_disjointed [Fintype ι] (f : ι -> α) : univ.sup (disjointed f) 
= univ.sup f
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_biUnion`：sup_biUnion [DecidableEq β] (s : Finset γ) (t : γ ->
 Finset β) : (s.biUnion t).sup f = s.sup fun x => (t x).sup f
· 使用定理 `Finset.sup_congr`：sup_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall 
a in s₂, f a = g a) : s₁.sup f = s₂.sup g
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用引理 `partialSups_apply`：partialSups_apply (f : ι -> α) (i : ι) : partialSups 
f i = (Iic i).sup' nonempty_Iic f
· 使用定理 `partialSups_disjointed`：partialSups_disjointed (f : ι -> α) : partialSup
s (disjointed f) = partialSups f
-/
lemma Fintype.sup_disjointed [Fintype ι] (f : ι → α) :
    univ.sup (disjointed f) = univ.sup f := by
  classical
  have hun : univ.biUnion Iic = (univ : Finset ι) := by
    ext r; simpa only [mem_biUnion, mem_univ, mem_Iic, true_and, iff_true] using ⟨r, le_rfl⟩
  rw [← hun, sup_biUnion, sup_biUnion, sup_congr rfl (fun i _ ↦ ?_)]
  rw [← sup'_eq_sup nonempty_Iic, ← sup'_eq_sup nonempty_Iic,
    ← partialSups_apply, ← partialSups_apply, partialSups_disjointed]
/-
**disjointed_partialSups** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjointed_partialSups (f : ι -> α) : disjointed (partialSups f) = disjoin
ted f
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_eq_symm`：sdiff_eq_symm (hy : y <= x) (h : x \ y = z) : x \ z = y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `le_partialSups`：le_partialSups (f : ι -> α) : f <= partialSups f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `partialSups_apply`：partialSups_apply (f : ι -> α) (i : ι) : partialSups 
f i = (Iic i).sup' nonempty_Iic f
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `sdiff_sdiff_eq_sdiff_sup`：sdiff_sdiff_eq_sdiff_sup (h : z <= x) : x \ (y
 \ z) = x \ y ⊔ z
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `Finset.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.notMem_Iio_self`：notMem_Iio_self {b : α} : b ∉ Iio b
· 使用定理 `Finset.Iic_eq_cons_Iio`：Iic_eq_cons_Iio (b : α) : Iic b = (Iio b).cons b
 notMem_Iio_self
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `sup_sdiff_left_self`：sup_sdiff_left_self : (a ⊔ b) \ a = b \ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma disjointed_partialSups (f : ι → α) :
    disjointed (partialSups f) = disjointed f := by
  classical
  ext i
  have step1 : f i \ (Iio i).sup f = partialSups f i \ (Iio i).sup f := by
    rw [sdiff_eq_symm (sdiff_le.trans (le_partialSups f i))]
    simp only [funext (partialSups_apply f), sup'_eq_sup]
    rw [sdiff_sdiff_eq_sdiff_sup (sup_mono Iio_subset_Iic_self), sup_eq_right]
    simp only [Iic_eq_cons_Iio, sup_cons, sup_sdiff_left_self, sdiff_le_iff, le_sup_right]
  simp only [disjointed_apply, step1, funext (partialSups_apply f), sup'_eq_sup, ← sup_biUnion]
  congr 2 with r
  simpa only [mem_biUnion, mem_Iio, mem_Iic] using
    ⟨fun ⟨a, ha⟩ ↦ ha.2.trans_lt ha.1, fun hr ↦ ⟨r, hr, le_rfl⟩⟩

/-- `disjointed f` is the unique map `d : ι → α` such that `d` has the same partial sups as `f`,
and `d i` and `d j` are disjoint whenever `i < j`. -/
/-
**disjointed_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjointed_unique {f d : ι -> α} (hdisj : forall {i j : ι} (_ : i < j), Di
sjoint (d i) (d j)) (hsups : partialSups d = partialSups f) : d = disjointed f
参数：hdisj : forall {i j : ι} (_ : i < j), Disjoint (d i) (d j)；hsups : partialSup
s d = partialSups f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `disjointed_partialSups`：disjointed_partialSups (f : ι -> α) : disjointed
 (partialSups f) = disjointed f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `disjointed_eq_self`：disjointed_eq_self {f : ι -> α} {i : ι} (hf : forall
 j < i, Disjoint (f j) (f i)) : disjointed f i = f i

--- 原说明 ---
`disjointed f` is the unique map `d : ι → α` such that `d` has the same partial 
sups as `f`,
and `d i` and `d j` are disjoint whenever `i < j`.
-/
theorem disjointed_unique {f d : ι → α} (hdisj : ∀ {i j : ι} (_ : i < j), Disjoint (d i) (d j))
    (hsups : partialSups d = partialSups f) :
    d = disjointed f := by
  rw [← disjointed_partialSups, ← hsups, disjointed_partialSups]
  exact funext fun _ ↦ (disjointed_eq_self (fun _ hj ↦ hdisj hj)).symm
/-
**biUnion_Iic_disjointed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：biUnion_Iic_disjointed {α : Type*} (f : ι -> Set α) (n : ι) : (⋃ i in Fins
et.Iic n, disjointed f i) = partialSups f n
参数：f : ι -> Set α；n : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `partialSups_disjointed`：partialSups_disjointed (f : ι -> α) : partialSup
s (disjointed f) = partialSups f
· 使用定理 `partialSups_eq_biSup`：partialSups_eq_biSup (f : ι -> α) (i : ι) : partia
lSups f i = ⨆ j <= i, f j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma biUnion_Iic_disjointed {α : Type*} (f : ι → Set α) (n : ι) :
    (⋃ i ∈ Finset.Iic n, disjointed f i) = partialSups f n := by
  rw [← partialSups_disjointed, partialSups_eq_biSup]
  simp
/-
**biUnion_range_succ_disjointed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：biUnion_range_succ_disjointed {α : Type*} (f : Nat -> Set α) (n : Nat) : (
⋃ i in Finset.range (n + 1), disjointed f i) = partialSups f n
参数：f : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.range_succ_eq_Iic`：range_succ_eq_Iic (n : Nat) : range (n + 1) = Iic
 n
· 使用引理 `biUnion_Iic_disjointed`：biUnion_Iic_disjointed {α : Type*} (f : ι -> Set
 α) (n : ι) : (⋃ i in Finset.Iic n, disjointed f i) = partialSups f n
-/
lemma biUnion_range_succ_disjointed {α : Type*} (f : ℕ → Set α) (n : ℕ) :
    (⋃ i ∈ Finset.range (n + 1), disjointed f i) = partialSups f n := by
  rw [Nat.range_succ_eq_Iic, biUnion_Iic_disjointed]

end PartialOrder

section LinearOrder -- the index type is a linear order

/-!
### Linear orders
-/

variable [LinearOrder ι] [LocallyFiniteOrderBot ι]

/-
**disjoint_disjointed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoint on disjointed f)
参数：f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pairwise_disjoint_on`：pairwise_disjoint_on [PartialOrder α] [OrderBot α]
 [LinearOrder ι] (f : ι -> α) : Pairwise (Disjoint on f) ↔ forall ⦃m n⦄, m < n -
> Disjoint…
· 使用定理 `disjoint_disjointed_of_lt`：disjoint_disjointed_of_lt (f : ι -> α) {i j :
 ι} (h : i < j) : Disjoint (disjointed f i) (disjointed f j)
-/
theorem disjoint_disjointed (f : ι → α) : Pairwise (Disjoint on disjointed f) :=
  (pairwise_disjoint_on _).mpr fun _ _ ↦ disjoint_disjointed_of_lt f

/-- `disjointed f` is the unique sequence that is pairwise disjoint and has the same partial sups
as `f`. -/
/-
**disjointed_unique'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjointed_unique' {f d : ι -> α} (hdisj : Pairwise (Disjoint on d)) (hsup
s : partialSups d = partialSups f) : d = disjointed f
参数：hdisj : Pairwise (Disjoint on d)；hsups : partialSups d = partialSups f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjointed_unique`：disjointed_unique {f d : ι -> α} (hdisj : forall {i j
 : ι} (_ : i < j), Disjoint (d i) (d j)) (hsups : partialSups d = partialSups f)
 : d = …
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b

--- 原说明 ---
`disjointed f` is the unique sequence that is pairwise disjoint and has the same
 partial sups
as `f`.
-/
theorem disjointed_unique' {f d : ι → α} (hdisj : Pairwise (Disjoint on d))
    (hsups : partialSups d = partialSups f) : d = disjointed f :=
  disjointed_unique (fun hij ↦ hdisj hij.ne) hsups

set_option backward.isDefEq.respectTransparency false in
omit [GeneralizedBooleanAlgebra α] in
/-
**Finset.disjiUnion_Iic_disjointed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.disjiUnion_Iic_disjointed [DecidableEq α] (n : ι) (t : ι -> Finset 
α) : (Iic n).disjiUnion (disjointed t) ((disjoint_disjointed t).set_pairwise _) 
= partialSups t n
参数：n : ι；t : ι -> Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pairwise.set_pairwise`：Pairwise.set_pairwise (hl : Pairwise R l) [Std.Sy
mm R] : { x | x in l }.Pairwise R
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `partialSups_disjointed`：partialSups_disjointed (f : ι -> α) : partialSup
s (disjointed f) = partialSups f
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用引理 `partialSups_apply`：partialSups_apply (f : ι -> α) (i : ι) : partialSups 
f i = (Iic i).sup' nonempty_Iic f
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Finset.sup_eq_biUnion`：sup_eq_biUnion {α β} [DecidableEq β] (s : Finset 
α) (t : α -> Finset β) : s.sup t = s.biUnion t
· 使用引理 `Finset.disjiUnion_eq_biUnion`：disjiUnion_eq_biUnion (s : Finset α) (f : 
α -> Finset β) (hf) : s.disjiUnion f hf = s.biUnion f
-/
lemma Finset.disjiUnion_Iic_disjointed [DecidableEq α] (n : ι) (t : ι → Finset α) :
    (Iic n).disjiUnion (disjointed t) ((disjoint_disjointed t).set_pairwise _) =
      partialSups t n := by
  rw [← partialSups_disjointed, partialSups_apply, Finset.sup'_eq_sup, Finset.sup_eq_biUnion,
    disjiUnion_eq_biUnion]

section SuccOrder

variable [SuccOrder ι]

/-
**disjointed_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjointed_succ (f : ι -> α) {i : ι} (hi : ¬IsMax i) : disjointed f (succ 
i) = f (succ i) \ partialSups f i
参数：f : ι -> α；hi : ¬IsMax i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `disjointed_apply`：disjointed_apply (f : ι -> α) (i : ι) : disjointed f i
 = f i \ (Iio i).sup f
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用引理 `partialSups_apply`：partialSups_apply (f : ι -> α) (i : ι) : partialSups 
f i = (Iic i).sup' nonempty_Iic f
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
-/
lemma disjointed_succ (f : ι → α) {i : ι} (hi : ¬IsMax i) :
    disjointed f (succ i) = f (succ i) \ partialSups f i := by
  rw [disjointed_apply, partialSups_apply, sup'_eq_sup]
  congr 2 with m
  simpa only [mem_Iio, mem_Iic] using lt_succ_iff_of_not_isMax hi
/-
**Monotone.disjointed_succ** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : GeneralizedBooleanAlgebra α] [inst
_1 : LinearOrder ι]   [inst_2 : LocallyFiniteOrderBot ι] [inst_3 : SuccOrder ι] 
{f : ι → α},   Monotone f → ∀ {i : ι}, ¬IsMax i → disjointed f (Order.succ i) = 
f (Order.succ i) \ f i
参数：Order.succ i；Order.succ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `disjointed_succ`：disjointed_succ (f : ι -> α) {i : ι} (hi : ¬IsMax i) : 
disjointed f (succ i) = f (succ i) \ partialSups f i
· 使用定理 `Monotone.partialSups_eq`：Monotone.partialSups_eq {f : ι -> α} (hf : Mono
tone f) : partialSups f = f
-/
protected lemma Monotone.disjointed_succ {f : ι → α} (hf : Monotone f) {i : ι} (hn : ¬IsMax i) :
    disjointed f (succ i) = f (succ i) \ f i := by
  rwa [disjointed_succ, hf.partialSups_eq]

/-- Note this lemma does not require `¬IsMax i`, unlike `disjointed_succ`. -/
/-
**Monotone.disjointed_succ_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.disjointed_succ_sup {f : ι -> α} (hf : Monotone f) (i : ι) : disj
ointed f (succ i) ⊔ f i = f (succ i)
参数：hf : Monotone f；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.succ_eq_iff_isMax`：succ_eq_iff_isMax : succ a = a ↔ IsMax a
· 使用定理 `disjointed_le`：disjointed_le (f : ι -> α) : disjointed f <= f
· 使用引理 `disjointed_apply`：disjointed_apply (f : ι -> α) (i : ι) : disjointed f i
 = f i \ (Iio i).sup f
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Order.lt_succ_iff_eq_or_lt_of_not_isMax`：lt_succ_iff_eq_or_lt_of_not_isM
ax (hb : ¬IsMax b) : a < succ b ↔ a = b ∨ a < b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用引理 `partialSups_apply`：partialSups_apply (f : ι -> α) (i : ι) : partialSups 
f i = (Iic i).sup' nonempty_Iic f
· 使用定理 `Monotone.partialSups_eq`：Monotone.partialSups_eq {f : ι -> α} (hf : Mono
tone f) : partialSups f = f
· 使用定理 `sdiff_sup_cancel`：sdiff_sup_cancel (h : b <= a) : a \ b ⊔ b = a
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a

--- 原说明 ---
Note this lemma does not require `¬IsMax i`, unlike `disjointed_succ`.
-/
lemma Monotone.disjointed_succ_sup {f : ι → α} (hf : Monotone f) (i : ι) :
    disjointed f (succ i) ⊔ f i = f (succ i) := by
  by_cases h : IsMax i
  · simpa only [succ_eq_iff_isMax.mpr h, sup_eq_right] using disjointed_le f i
  · rw [disjointed_apply]
    have : Iio (succ i) = Iic i := by
      ext
      simp only [mem_Iio, lt_succ_iff_eq_or_lt_of_not_isMax h, mem_Iic, le_iff_lt_or_eq, Or.comm]
    rw [this, ← sup'_eq_sup nonempty_Iic, ← partialSups_apply, hf.partialSups_eq,
      sdiff_sup_cancel <| hf <| le_succ i]

end SuccOrder

/-
**sup_Ioc_disjointed_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sup_Ioc_disjointed_of_monotone {ι : Type*} [LinearOrder ι] [LocallyFiniteO
rder ι] [OrderBot ι] {f : ι -> α} (hf : Monotone f) {m n : ι} (hm : n <= m) : (F
inset.Ioc n m).sup (disjointed f) = f m \ f n
参数：hf : Monotone f；hm : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Succ.rec`：Succ.rec {m : α} {P : forall n, m <= n -> Prop} (rfl : P m le_
rfl) (succ : forall n (hmn : m <= n), P n hmn -> P (succ n) (hmn.trans <| le_s…
· 使用定理 `LinearLocallyFiniteOrder.instIsSuccArchimedeanOfLocallyFiniteOrder`：∀ {ι
 : Type u_1} [inst : LinearOrder ι] [LocallyFiniteOrder ι] [inst_2 : SuccOrder ι
], IsSuccArchimedean ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.Ioc_eq_empty_of_le`：Ioc_eq_empty_of_le (h : b <= a) : Ioc a b = ∅
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.succ_eq_iff_isMax`：succ_eq_iff_isMax : succ a = a ↔ IsMax a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.insert_Ioc_right_eq_Ioc_succ_of_not_isMax`：insert_Ioc_right_eq_Io
c_succ_of_not_isMax (h : a <= b) (hb : ¬ IsMax b) : insert (succ b) (Ioc a b) = 
Ioc a (succ b)
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Monotone.disjointed_succ`：∀ {α : Type u_1} {ι : Type u_2} [inst : Genera
lizedBooleanAlgebra α] [inst_1 : LinearOrder ι]   [inst_2 : LocallyFiniteOrderBo
t ι] [inst_3 :…
· 使用定理 `sdiff_sup_sdiff_cancel`：sdiff_sup_sdiff_cancel (hba : b <= a) (hcb : c <
= b) : a \ b ⊔ b \ c = a \ c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
-/
lemma sup_Ioc_disjointed_of_monotone
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    {f : ι → α} (hf : Monotone f) {m n : ι} (hm : n ≤ m) :
    (Finset.Ioc n m).sup (disjointed f) = f m \ f n := by
  let : SuccOrder ι := LinearLocallyFiniteOrder.succOrder ι
  induction hm using Succ.rec with
  | rfl => simp
  | succ m hm ih =>
    by_cases h'm : IsMax m
    · simpa [Order.succ_eq_iff_isMax.mpr h'm] using ih
    · rw [← Finset.insert_Ioc_right_eq_Ioc_succ_of_not_isMax hm h'm]
      simp only [sup_insert, hf.disjointed_succ h'm, ih]
      exact sdiff_sup_sdiff_cancel (hf (Order.le_succ m)) (hf hm)
/-
**biUnion_Ioc_disjointed_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：biUnion_Ioc_disjointed_of_monotone {α ι : Type*} [LinearOrder ι] [LocallyF
initeOrder ι] [OrderBot ι] {f : ι -> Set α} (hf : Monotone f) {m n : ι} (hm : n 
<= m) : ⋃ i in Finset.Ioc n m, disjointed f i = f m \ f n
参数：hf : Monotone f；hm : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sup_Ioc_disjointed_of_monotone`：sup_Ioc_disjointed_of_monotone {ι : Type
*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι] {f : ι -> α} (hf : Monoto
ne f) {m n : ι} (hm …
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma biUnion_Ioc_disjointed_of_monotone
    {α ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    {f : ι → Set α} (hf : Monotone f) {m n : ι} (hm : n ≤ m) :
    ⋃ i ∈ Finset.Ioc n m, disjointed f i = f m \ f n := by
  simp [← sup_Ioc_disjointed_of_monotone hf hm]

end LinearOrder

/-!
### Functions on an arbitrary fintype
-/

/-- For any finite family of elements `f : ι → α`, we can find a pairwise-disjoint family `g`
bounded above by `f` and having the same supremum. This is non-canonical, depending on an arbitrary
choice of ordering of `ι`. -/
/-
**Fintype.exists_disjointed_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fintype.exists_disjointed_le {ι : Type*} [Fintype ι] (f : ι -> α) : exists
 g, g <= f ∧ univ.sup g = univ.sup f ∧ Pairwise (Disjoint on g)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Subsingleton.pairwise`：∀ {α : Type u_1} {r : α → α → Prop} [Subsingleton
 α], Pairwise r
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `disjointed_le`：disjointed_le (f : ι -> α) : disjointed f <= f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.image_univ_equiv`：image_univ_equiv [Fintype β] (f : β ≃ α) : univ
.image f = univ
· 使用引理 `Fintype.sup_disjointed`：Fintype.sup_disjointed [Fintype ι] (f : ι -> α) 
: univ.sup (disjointed f) = univ.sup f
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
For any finite family of elements `f : ι → α`, we can find a pairwise-disjoint f
amily `g`
bounded above by `f` and having the same supremum. This is non-canonical, depend
ing on an arbitrary
choice of ordering of `ι`.
-/
lemma Fintype.exists_disjointed_le {ι : Type*} [Fintype ι] (f : ι → α) :
    ∃ g, g ≤ f ∧ univ.sup g = univ.sup f ∧ Pairwise (Disjoint on g) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  ·  -- do `ι = ∅` separately since `⊤ : Fin n` isn't defined for `n = 0`
    exact ⟨f, le_rfl, rfl, Subsingleton.pairwise⟩
  let R : ι ≃ Fin _ := equivFin ι
  let f' : Fin _ → α := f ∘ R.symm
  have hf' : f = f' ∘ R := by ext; simp only [Function.comp_apply, Equiv.symm_apply_apply, f']
  refine ⟨disjointed f' ∘ R, ?_, ?_, ?_⟩
  · intro n
    simpa only [hf'] using! disjointed_le f' (R n)
  · simpa only [← sup_image, image_univ_equiv, hf'] using! sup_disjointed f'
  · exact fun i j hij ↦ disjoint_disjointed f' (R.injective.ne hij)

end GeneralizedBooleanAlgebra

section CompleteBooleanAlgebra

/-! ### Complete Boolean algebras -/

variable [CompleteBooleanAlgebra α]

/-
**iSup_disjointed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_disjointed [PartialOrder ι] [LocallyFiniteOrderBot ι] (f : ι -> α) : 
⨆ i, disjointed f i = ⨆ i, f i
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_eq_iSup_of_partialSups_eq_partialSups`：iSup_eq_iSup_of_partialSups_
eq_partialSups {f g : ι -> α} (h : partialSups f = partialSups g) : ⨆ i, f i = ⨆
 i, g i
· 使用定理 `partialSups_disjointed`：partialSups_disjointed (f : ι -> α) : partialSup
s (disjointed f) = partialSups f
-/
theorem iSup_disjointed [PartialOrder ι] [LocallyFiniteOrderBot ι] (f : ι → α) :
    ⨆ i, disjointed f i = ⨆ i, f i :=
  iSup_eq_iSup_of_partialSups_eq_partialSups (partialSups_disjointed f)
/-
**disjointed_eq_inf_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjointed_eq_inf_compl [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι -> α
) (i : ι) : disjointed f i = f i ⊓ ⨅ j < i, (f j)ᶜ
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `compl_iSup`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iSup f)ᶜ = ⨅ i, (f i)ᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem disjointed_eq_inf_compl [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι → α) (i : ι) :
    disjointed f i = f i ⊓ ⨅ j < i, (f j)ᶜ := by
  simp only [disjointed_apply, Finset.sup_eq_iSup, mem_Iio, sdiff_eq, compl_iSup]

end CompleteBooleanAlgebra

section Set

/-! ### Lemmas specific to set-valued functions -/

/-
**disjointed_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjointed_subset [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι -> Set α) 
(i : ι) : disjointed f i subseteq f i
参数：f : ι -> Set α；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjointed_le`：disjointed_le (f : ι -> α) : disjointed f <= f

--- 原说明 ---
### Lemmas specific to set-valued functions
-/
theorem disjointed_subset [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι → Set α) (i : ι) :
    disjointed f i ⊆ f i :=
  disjointed_le f i
/-
**iUnion_disjointed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrderBot ι] {f : ι -> Set
 α} : ⋃ i, disjointed f i = ⋃ i, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_disjointed`：iSup_disjointed [PartialOrder ι] [LocallyFiniteOrderBot
 ι] (f : ι -> α) : ⨆ i, disjointed f i = ⨆ i, f i
-/
theorem iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrderBot ι] {f : ι → Set α} :
    ⋃ i, disjointed f i = ⋃ i, f i :=
  iSup_disjointed f
/-
**disjointed_eq_inter_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjointed_eq_inter_compl [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι ->
 Set α) (i : ι) : disjointed f i = f i inter ⋂ j < i, (f j)ᶜ
参数：f : ι -> Set α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjointed_eq_inf_compl`：disjointed_eq_inf_compl [Preorder ι] [LocallyFi
niteOrderBot ι] (f : ι -> α) (i : ι) : disjointed f i = f i ⊓ ⨅ j < i, (f j)ᶜ
-/
theorem disjointed_eq_inter_compl [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι → Set α) (i : ι) :
    disjointed f i = f i ∩ ⋂ j < i, (f j)ᶜ :=
  disjointed_eq_inf_compl f i
/-
**preimage_find_eq_disjointed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_find_eq_disjointed (s : Nat -> Set α) (H : forall x, exists n, x 
in s n) [forall x n, Decidable (x in s n)] (n : Nat) : (fun x => Nat.find (H x))
 ⁻¹' {n} = disjointed s n
参数：s : Nat -> Set α；H : forall x, exists n, x in s n；x in s n；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `disjointed_eq_inter_compl`：disjointed_eq_inter_compl [Preorder ι] [Local
lyFiniteOrderBot ι] (f : ι -> Set α) (i : ι) : disjointed f i = f i inter ⋂ j < 
i, (f j)ᶜ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_find_eq_disjointed (s : ℕ → Set α) (H : ∀ x, ∃ n, x ∈ s n)
    [∀ x n, Decidable (x ∈ s n)] (n : ℕ) : (fun x => Nat.find (H x)) ⁻¹' {n} = disjointed s n := by
  ext x
  simp [Nat.find_eq_iff, disjointed_eq_inter_compl]

end Set

section Nat

/-!
### Functions on `ℕ`

(See also `Mathlib/Algebra/Order/Disjointed.lean` for results with more algebra pre-requisites.)
-/

variable [GeneralizedBooleanAlgebra α]

@[simp]
/-
**disjointed_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjointed_zero (f : Nat -> α) : disjointed f 0 = f 0
参数：f : Nat -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjointed_bot`：∀ {α : Type u_1} {ι : Type u_2} [inst : GeneralizedBoole
anAlgebra α] [inst_1 : Preorder ι]   [inst_2 : LocallyFiniteOrderBot ι] [inst_3 
: Or…
-/
theorem disjointed_zero (f : ℕ → α) : disjointed f 0 = f 0 :=
  disjointed_bot f

end Nat

