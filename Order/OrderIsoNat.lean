/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Logic.Denumerable
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Lattice.Nat

/-!
# Relation embeddings from the naturals

This file allows translation from monotone functions `ℕ → α` to order embeddings `ℕ ↪ α` and
defines the limit value of an eventually-constant sequence.

## Main declarations

* `natLT`/`natGT`: Make an order embedding `Nat ↪ α` from
  an increasing/decreasing function `Nat → α`.
* `Infinite.exists_strictMono_or_strictAnti`: Every infinite linear order contains a strictly
  increasing or strictly decreasing sequence indexed by `ℕ`.
* `Finite.of_wellFoundedLT_wellFoundedGT`: A linear order that is well-founded in both directions
  is finite.
* `monotonicSequenceLimit`: The limit of an eventually-constant monotone sequence `Nat →o α`.
* `monotonicSequenceLimitIndex`: The index of the first occurrence of `monotonicSequenceLimit`
  in the sequence.
-/

@[expose] public section


variable {α : Type*}

namespace RelEmbedding

variable {r : α → α → Prop} [IsStrictOrder α r]

/-- If `f` is a strictly `r`-increasing sequence, then this returns `f` as an order embedding. -/
/-
**RelEmbedding.natLT** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：natLT (f : Nat -> α) (H : forall n : Nat, r (f n) (f (n + 1))) : ((· < ·) 
: Nat -> Nat -> Prop) ↪r r
参数：f : Nat -> α；H : forall n : Nat, r (f n) (f (n + 1))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instTrichotomousLt`：Std.Trichotomous fun x1 x2 => x1 < x2

--- 原说明 ---
If `f` is a strictly `r`-increasing sequence, then this returns `f` as an order 
embedding.
-/
def natLT (f : ℕ → α) (H : ∀ n : ℕ, r (f n) (f (n + 1))) : ((· < ·) : ℕ → ℕ → Prop) ↪r r :=
  ofMonotone f <| Nat.rel_of_forall_rel_succ_of_lt r H

@[simp]
/-
**RelEmbedding.coe_natLT** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：coe_natLT {f : Nat -> α} {H : forall n : Nat, r (f n) (f (n + 1))} : ⇑(nat
LT f H) = f
参数：f n；f (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_natLT {f : ℕ → α} {H : ∀ n : ℕ, r (f n) (f (n + 1))} : ⇑(natLT f H) = f :=
  rfl

/-- If `f` is a strictly `r`-decreasing sequence, then this returns `f` as an order embedding. -/
/-
**RelEmbedding.natGT** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：natGT (f : Nat -> α) (H : forall n : Nat, r (f (n + 1)) (f n)) : ((· > ·) 
: Nat -> Nat -> Prop) ↪r r
参数：f : Nat -> α；H : forall n : Nat, r (f (n + 1)) (f n)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instIsStrictOrderSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) 
[IsStrictOrder α r], IsStrictOrder α (Function.swap r)

--- 原说明 ---
If `f` is a strictly `r`-decreasing sequence, then this returns `f` as an order 
embedding.
-/
def natGT (f : ℕ → α) (H : ∀ n : ℕ, r (f (n + 1)) (f n)) : ((· > ·) : ℕ → ℕ → Prop) ↪r r :=
  RelEmbedding.swap (natLT f H)

@[simp]
/-
**RelEmbedding.coe_natGT** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：coe_natGT {f : Nat -> α} {H : forall n : Nat, r (f (n + 1)) (f n)} : ⇑(nat
GT f H) = f
参数：f (n + 1)；f n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_natGT {f : ℕ → α} {H : ∀ n : ℕ, r (f (n + 1)) (f n)} : ⇑(natGT f H) = f :=
  rfl

/-- A value is accessible iff it isn't contained in any infinite decreasing sequence. -/
/-
**RelEmbedding.acc_iff_isEmpty_subtype_mem_range** 是 Mathlib 中的一个定理，位于命名空间 `RelE
mbedding`。
形式化陈述：acc_iff_isEmpty_subtype_mem_range {x} : Acc r x ↔ IsEmpty { f : ((· > ·) :
 Nat -> Nat -> Prop) ↪r r // x in Set.range f } where mp acc
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_acc_iff_exists_descending_chain`：not_acc_iff_exists_descending_chain
 {α} {r : α -> α -> Prop} {x : α} : ¬Acc r x ↔ exists f : Nat -> α, f 0 = x ∧ fo
rall n, r (f (n + 1)) (f …
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A value is accessible iff it isn't contained in any infinite decreasing sequence
.
-/
theorem acc_iff_isEmpty_subtype_mem_range {x} :
    Acc r x ↔ IsEmpty { f : ((· > ·) : ℕ → ℕ → Prop) ↪r r // x ∈ Set.range f } where
  mp acc := .mk fun ⟨f, k, hk⟩ ↦ not_acc_iff_exists_descending_chain.mpr
    ⟨(f <| k + ·), hk, fun _n ↦ f.map_rel_iff.2 (Nat.lt_succ_self _)⟩ acc
  mpr h := of_not_not fun nacc ↦
    have ⟨f, hf⟩ := not_acc_iff_exists_descending_chain.mp nacc
    h.elim ⟨natGT f hf.2, 0, hf.1⟩
/-
**RelEmbedding.not_acc** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：not_acc (f : ((· > ·) : Nat -> Nat -> Prop) ↪r r) (k : Nat) : ¬Acc r (f k)
参数：f : ((· > ·) : Nat -> Nat -> Prop) ↪r r；k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelEmbedding.acc_iff_isEmpty_subtype_mem_range`：acc_iff_isEmpty_subtype_
mem_range {x} : Acc r x ↔ IsEmpty { f : ((· > ·) : Nat -> Nat -> Prop) ↪r r // x
 in Set.range f } where mp acc
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
-/
theorem not_acc (f : ((· > ·) : ℕ → ℕ → Prop) ↪r r) (k : ℕ) : ¬Acc r (f k) := by
  rw [acc_iff_isEmpty_subtype_mem_range, not_isEmpty_iff]
  exact ⟨⟨f, k, rfl⟩⟩

/-- A strict order relation is well-founded iff it doesn't have any infinite descending chain.

See `wellFounded_iff_isEmpty_descending_chain` for a version which works on any relation. -/
/-
**RelEmbedding.wellFounded_iff_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：wellFounded_iff_isEmpty : WellFounded r ↔ IsEmpty (((· > ·) : Nat -> Nat -
> Prop) ↪r r) where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.not_acc`：not_acc (f : ((· > ·) : Nat -> Nat -> Prop) ↪r r) 
(k : Nat) : ¬Acc r (f k)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RelEmbedding.acc_iff_isEmpty_subtype_mem_range`：acc_iff_isEmpty_subtype_
mem_range {x} : Acc r x ↔ IsEmpty { f : ((· > ·) : Nat -> Nat -> Prop) ↪r r // x
 in Set.range f } where mp acc
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)

--- 原说明 ---
A strict order relation is well-founded iff it doesn't have any infinite descend
ing chain.

See `wellFounded_iff_isEmpty_descending_chain` for a version which works on any 
relation.
-/
theorem wellFounded_iff_isEmpty :
    WellFounded r ↔ IsEmpty (((· > ·) : ℕ → ℕ → Prop) ↪r r) where
  mp := fun ⟨h⟩ ↦ ⟨fun f ↦ f.not_acc 0 (h _)⟩
  mpr _ := ⟨fun _x ↦ acc_iff_isEmpty_subtype_mem_range.2 inferInstance⟩
/-
**RelEmbedding.not_wellFounded** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：not_wellFounded (f : ((· > ·) : Nat -> Nat -> Prop) ↪r r) : ¬WellFounded r
参数：f : ((· > ·) : Nat -> Nat -> Prop) ↪r r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelEmbedding.wellFounded_iff_isEmpty`：wellFounded_iff_isEmpty : WellFoun
ded r ↔ IsEmpty (((· > ·) : Nat -> Nat -> Prop) ↪r r) where mp
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
-/
theorem not_wellFounded (f : ((· > ·) : ℕ → ℕ → Prop) ↪r r) : ¬WellFounded r := by
  rw [wellFounded_iff_isEmpty, not_isEmpty_iff]
  exact ⟨f⟩

end RelEmbedding

/-
**not_strictAnti_of_wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_strictAnti_of_wellFoundedLT [Preorder α] [WellFoundedLT α] (f : Nat ->
 α) : ¬ StrictAnti f
参数：f : Nat -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.not_wellFounded`：not_wellFounded (f : ((· > ·) : Nat -> Nat
 -> Prop) ↪r r) : ¬WellFounded r
· 使用定理 `instIsStrictOrderLt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x1 < x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
-/
theorem not_strictAnti_of_wellFoundedLT [Preorder α] [WellFoundedLT α] (f : ℕ → α) :
    ¬ StrictAnti f := fun hf ↦
  (RelEmbedding.natGT f (fun n ↦ hf (by simp))).not_wellFounded wellFounded_lt
/-
**not_strictMono_of_wellFoundedGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_strictMono_of_wellFoundedGT [Preorder α] [WellFoundedGT α] (f : Nat ->
 α) : ¬ StrictMono f
参数：f : Nat -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_strictAnti_of_wellFoundedLT`：not_strictAnti_of_wellFoundedLT [Preord
er α] [WellFoundedLT α] (f : Nat -> α) : ¬ StrictAnti f
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
theorem not_strictMono_of_wellFoundedGT [Preorder α] [WellFoundedGT α] (f : ℕ → α) :
    ¬ StrictMono f :=
  not_strictAnti_of_wellFoundedLT (α := αᵒᵈ) f

namespace Nat

variable (s : Set ℕ) [Infinite s]

/-- An order embedding from `ℕ` to itself with a specified range -/
/-
**Nat.orderEmbeddingOfSet** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：orderEmbeddingOfSet [DecidablePred (· in s)] : Nat ↪o Nat
参数：· in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order embedding from `ℕ` to itself with a specified range
-/
def orderEmbeddingOfSet [DecidablePred (· ∈ s)] : ℕ ↪o ℕ :=
  (RelEmbedding.orderEmbeddingOfLTEmbedding
    (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun _ => Nat.Subtype.lt_succ_self _)).trans
    (OrderEmbedding.subtype (· ∈ s))

/-- `Nat.Subtype.ofNat` as an order isomorphism between `ℕ` and an infinite subset. See also
`Nat.nth` for a version where the subset may be finite. -/
/-
**Nat.Subtype.orderIsoOfNat** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Subtype`。
形式化陈述：(s : Set ℕ) → [Infinite ↑s] → ℕ ≃o ↑s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nat.Subtype.ofNat` as an order isomorphism between `ℕ` and an infinite subset. 
See also
`Nat.nth` for a version where the subset may be finite.
-/
noncomputable def Subtype.orderIsoOfNat : ℕ ≃o s := by
  classical
  exact
    RelIso.ofSurjective
      (RelEmbedding.orderEmbeddingOfLTEmbedding
        (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun n => Nat.Subtype.lt_succ_self _))
      Nat.Subtype.ofNat_surjective

variable {s}

@[simp]
/-
**Nat.coe_orderEmbeddingOfSet** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coe_orderEmbeddingOfSet [DecidablePred (· in s)] : ⇑(orderEmbeddingOfSet s
) = (↑) ∘ Subtype.ofNat s
参数：· in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_orderEmbeddingOfSet [DecidablePred (· ∈ s)] :
    ⇑(orderEmbeddingOfSet s) = (↑) ∘ Subtype.ofNat s :=
  rfl
/-
**Nat.orderEmbeddingOfSet_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：orderEmbeddingOfSet_apply [DecidablePred (· in s)] {n : Nat} : orderEmbedd
ingOfSet s n = Subtype.ofNat s n
参数：· in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderEmbeddingOfSet_apply [DecidablePred (· ∈ s)] {n : ℕ} :
    orderEmbeddingOfSet s n = Subtype.ofNat s n :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Nat.Subtype.orderIsoOfNat_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Subtype`。
形式化陈述：∀ {s : Set ℕ} [inst : Infinite ↑s] [dP : DecidablePred fun x => x ∈ s] {n 
: ℕ},   (Nat.Subtype.orderIsoOfNat s) n = Nat.Subtype.ofNat s n
参数：Nat.Subtype.orderIsoOfNat s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelIso.ofSurjective_apply`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → 
Prop} {s : β → β → Prop} (f : r ↪r s) (H : Function.Surjective ⇑f) (a : α),   (R
elIso.ofSurject…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
theorem Subtype.orderIsoOfNat_apply [dP : DecidablePred (· ∈ s)] {n : ℕ} :
    Subtype.orderIsoOfNat s n = Subtype.ofNat s n := by
  simp only [orderIsoOfNat, RelIso.ofSurjective_apply,
    RelEmbedding.orderEmbeddingOfLTEmbedding_apply, RelEmbedding.coe_natLT]
  congr!

variable (s)
/-
**Nat.orderEmbeddingOfSet_range** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：orderEmbeddingOfSet_range [DecidablePred (· in s)] : Set.range (Nat.orderE
mbeddingOfSet s) = s
参数：· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Subtype.coe_comp_ofNat_range`：coe_comp_ofNat_range : Set.range ((↑) 
∘ ofNat s : Nat -> Nat) = s
-/
theorem orderEmbeddingOfSet_range [DecidablePred (· ∈ s)] :
    Set.range (Nat.orderEmbeddingOfSet s) = s :=
  Subtype.coe_comp_ofNat_range
/-
**Nat.exists_subseq_of_forall_mem_union** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_subseq_of_forall_mem_union {s t : Set α} (e : Nat -> α) (he : foral
l n, e n in s union t) : exists g : Nat ↪o Nat, (forall n, e (g n) in s) ∨ foral
l n, e (g n) in t
参数：e : Nat -> α；he : forall n, e n in s union t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem exists_subseq_of_forall_mem_union {s t : Set α} (e : ℕ → α) (he : ∀ n, e n ∈ s ∪ t) :
    ∃ g : ℕ ↪o ℕ, (∀ n, e (g n) ∈ s) ∨ ∀ n, e (g n) ∈ t := by
  classical
    have : Infinite (e ⁻¹' s) ∨ Infinite (e ⁻¹' t) := by
      simp only [Set.infinite_coe_iff, ← Set.infinite_union, ← Set.preimage_union,
        Set.eq_univ_of_forall fun n => Set.mem_preimage.2 (he n), Set.infinite_univ]
    cases this
    exacts [⟨Nat.orderEmbeddingOfSet (e ⁻¹' s), Or.inl fun n => (Nat.Subtype.ofNat (e ⁻¹' s) _).2⟩,
      ⟨Nat.orderEmbeddingOfSet (e ⁻¹' t), Or.inr fun n => (Nat.Subtype.ofNat (e ⁻¹' t) _).2⟩]

end Nat

/-
**exists_increasing_or_nonincreasing_subseq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_increasing_or_nonincreasing_subseq' (r : α -> α -> Prop) (f : Nat -
> α) : exists g : Nat ↪o Nat, (forall n : Nat, r (f (g n)) (f (g (n + 1)))) ∨ fo
rall m n : Nat, m < n -> ¬r (f (g m)) (f (g n))
参数：r : α -> α -> Prop；f : Nat -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.intro_right`：∀ {b : Prop} (a : Prop), b → a ∨ b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.orderEmbeddingOfSet_range`：orderEmbeddingOfSet_range [DecidablePred 
(· in s)] : Set.range (Nat.orderEmbeddingOfSet s) = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Set.Infinite.eq_1`：∀ {α : Type u} (s : Set α), s.Infinite = ¬s.Finite
· 使用定理 `Set.infinite_coe_iff`：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infi
nite
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Nat.not_succ_le_self`：∀ (n : ℕ), ¬n.succ ≤ n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsStrictOrderLt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x1 < x2
· 使用定理 `Nat.add_lt_add_right`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), n + k < m + k
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Or.intro_left`：∀ {a : Prop} (b : Prop), a → a ∨ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem exists_increasing_or_nonincreasing_subseq' (r : α → α → Prop) (f : ℕ → α) :
    ∃ g : ℕ ↪o ℕ,
      (∀ n : ℕ, r (f (g n)) (f (g (n + 1)))) ∨ ∀ m n : ℕ, m < n → ¬r (f (g m)) (f (g n)) := by
  classical
    let bad : Set ℕ := { m | ∀ n, m < n → ¬r (f m) (f n) }
    by_cases hbad : Infinite bad
    · refine ⟨Nat.orderEmbeddingOfSet bad, Or.intro_right _ fun m n mn => ?_⟩
      have h := @Set.mem_range_self _ _ ↑(Nat.orderEmbeddingOfSet bad) m
      rw [Nat.orderEmbeddingOfSet_range bad] at h
      exact h _ ((OrderEmbedding.lt_iff_lt _).2 mn)
    · rw [Set.infinite_coe_iff, Set.Infinite, not_not] at hbad
      obtain ⟨m, hm⟩ : ∃ m, ∀ n, m ≤ n → n ∉ bad := by
        by_cases he : hbad.toFinset.Nonempty
        · refine
            ⟨(hbad.toFinset.max' he).succ, fun n hn nbad =>
              Nat.not_succ_le_self _
                (hn.trans (hbad.toFinset.le_max' n (hbad.mem_toFinset.2 nbad)))⟩
        · exact ⟨0, fun n _ nbad => he ⟨n, hbad.mem_toFinset.2 nbad⟩⟩
      have h : ∀ n : ℕ, ∃ n' : ℕ, n < n' ∧ r (f (n + m)) (f (n' + m)) := by
        intro n
        have h := hm _ (Nat.le_add_left m n)
        simp only [bad, exists_prop, not_not, Set.mem_ofPred_eq, not_forall] at h
        obtain ⟨n', hn1, hn2⟩ := h
        refine ⟨n + n' - n - m, by lia, ?_⟩
        convert! hn2
        lia
      let g' : ℕ → ℕ := @Nat.rec (fun _ => ℕ) m fun n gn => Nat.find (h gn)
      exact
        ⟨(RelEmbedding.natLT (fun n => g' n + m) fun n =>
              Nat.add_lt_add_right (Nat.find_spec (h (g' n))).1 m).orderEmbeddingOfLTEmbedding,
          Or.intro_left _ fun n => (Nat.find_spec (h (g' n))).2⟩

/-- This is the infinitary Erdős–Szekeres theorem, and an important lemma in the usual proof of
Bolzano-Weierstrass for `ℝ`. -/
/-
**exists_increasing_or_nonincreasing_subseq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_increasing_or_nonincreasing_subseq (r : α -> α -> Prop) [IsTrans α 
r] (f : Nat -> α) : exists g : Nat ↪o Nat, (forall m n : Nat, m < n -> r (f (g m
)) (f (g n))) ∨ forall m n : Nat, m < n -> ¬r (f (g m)) (f (g n))
参数：r : α -> α -> Prop；f : Nat -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_increasing_or_nonincreasing_subseq'`：exists_increasing_or_nonincr
easing_subseq' (r : α -> α -> Prop) (f : Nat -> α) : exists g : Nat ↪o Nat, (for
all n : Nat, r (f (g n)) (f (g (…
· 使用定理 `Or.intro_left`：∀ {a : Prop} (b : Prop), a → a ∨ b
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.intro_right`：∀ {b : Prop} (a : Prop), b → a ∨ b

--- 原说明 ---
This is the infinitary Erdős–Szekeres theorem, and an important lemma in the usu
al proof of
Bolzano-Weierstrass for `ℝ`.
-/
theorem exists_increasing_or_nonincreasing_subseq (r : α → α → Prop) [IsTrans α r] (f : ℕ → α) :
    ∃ g : ℕ ↪o ℕ,
      (∀ m n : ℕ, m < n → r (f (g m)) (f (g n))) ∨ ∀ m n : ℕ, m < n → ¬r (f (g m)) (f (g n)) := by
  obtain ⟨g, hr | hnr⟩ := exists_increasing_or_nonincreasing_subseq' r f
  · refine ⟨g, Or.intro_left _ fun m n mn => ?_⟩
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.2 mn)
    induction x with
    | zero => apply hr
    | succ x ih =>
      apply IsTrans.trans _ _ _ _ (hr _)
      exact ih (lt_of_lt_of_le m.lt_succ_self (Nat.le_add_right _ _))
  · exact ⟨g, Or.intro_right _ hnr⟩

/-- Every infinite linear order contains either a strictly increasing or a strictly decreasing
sequence indexed by `ℕ`. -/
/-
**Infinite.exists_strictMono_or_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Infinite.exists_strictMono_or_strictAnti (α : Type*) [LinearOrder α] [Infi
nite α] : exists f : Nat -> α, StrictMono f ∨ StrictAnti f
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_increasing_or_nonincreasing_subseq`：exists_increasing_or_nonincre
asing_subseq (r : α -> α -> Prop) [IsTrans α r] (f : Nat -> α) : exists g : Nat 
↪o Nat, (forall m n : Nat, m < …
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f

--- 原说明 ---
Every infinite linear order contains either a strictly increasing or a strictly 
decreasing
sequence indexed by `ℕ`.
-/
theorem Infinite.exists_strictMono_or_strictAnti (α : Type*) [LinearOrder α] [Infinite α] :
    ∃ f : ℕ → α, StrictMono f ∨ StrictAnti f := by
  let f := Infinite.natEmbedding α
  obtain ⟨g, hg⟩ := exists_increasing_or_nonincreasing_subseq (· < ·) f
  refine ⟨f ∘ g, ?_⟩
  rcases hg with hIncreasing | hNonincreasing
  · exact Or.inl hIncreasing
  · refine Or.inr <| fun m n hmn ↦ lt_of_le_of_ne ?_ ((f.injective.comp g.injective).ne ?_)
    · grind
    · grind

/-- A linear order that is well-founded in both directions is finite. -/
/-
**Finite.of_wellFoundedLT_wellFoundedGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.of_wellFoundedLT_wellFoundedGT (α : Type*) [LinearOrder α] [WellFou
ndedLT α] [WellFoundedGT α] : Finite α
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_not_infinite`：∀ {α : Sort u_1}, ¬Infinite α → Finite α
· 使用定理 `Infinite.exists_strictMono_or_strictAnti`：Infinite.exists_strictMono_or_
strictAnti (α : Type*) [LinearOrder α] [Infinite α] : exists f : Nat -> α, Stric
tMono f ∨ StrictAnti f
· 使用定理 `not_strictMono_of_wellFoundedGT`：not_strictMono_of_wellFoundedGT [Preord
er α] [WellFoundedGT α] (f : Nat -> α) : ¬ StrictMono f
· 使用定理 `not_strictAnti_of_wellFoundedLT`：not_strictAnti_of_wellFoundedLT [Preord
er α] [WellFoundedLT α] (f : Nat -> α) : ¬ StrictAnti f

--- 原说明 ---
A linear order that is well-founded in both directions is finite.
-/
theorem Finite.of_wellFoundedLT_wellFoundedGT (α : Type*) [LinearOrder α]
    [WellFoundedLT α] [WellFoundedGT α] : Finite α := by
  apply Finite.of_not_infinite
  intro
  obtain ⟨f, hStrictMono | hStrictAnti⟩ := Infinite.exists_strictMono_or_strictAnti α
  · exact not_strictMono_of_wellFoundedGT f hStrictMono
  · exact not_strictAnti_of_wellFoundedLT f hStrictAnti

/-- The **monotone chain condition**: a preorder is co-well-founded iff every increasing sequence
contains two non-increasing indices.

See `wellFoundedGT_iff_monotone_chain_condition` for a stronger version on partial orders. -/
/-
**wellFoundedGT_iff_monotone_chain_condition'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellFoundedGT_iff_monotone_chain_condition' [Preorder α] : WellFoundedGT α
 ↔ forall a : Nat ->o α, exists n, forall m, n <= m -> ¬a n < a m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WellFoundedGT.eq_1`：∀ (α : Type u_1) [inst : LT α], WellFoundedGT α = Is
WellFounded α fun x1 x2 => x2 < x1
· 使用定理 `isWellFounded_iff`：∀ (α : Type u) (r : α → α → Prop), IsWellFounded α r 
↔ WellFounded r
· 使用定理 `RelEmbedding.wellFounded_iff_isEmpty`：wellFounded_iff_isEmpty : WellFoun
ded r ↔ IsEmpty (((· > ·) : Nat -> Nat -> Prop) ↪r r) where mp
· 使用定理 `instIsStrictOrderGt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x2 < x1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b

--- 原说明 ---
The **monotone chain condition**: a preorder is co-well-founded iff every increa
sing sequence
contains two non-increasing indices.

See `wellFoundedGT_iff_monotone_chain_condition` for a stronger version on parti
al orders.
-/
theorem wellFoundedGT_iff_monotone_chain_condition' [Preorder α] :
    WellFoundedGT α ↔ ∀ a : ℕ →o α, ∃ n, ∀ m, n ≤ m → ¬a n < a m := by
  refine ⟨fun h a => ?_, fun h => ?_⟩
  · obtain ⟨x, ⟨n, rfl⟩, H⟩ := h.wf.has_min _ (Set.range_nonempty a)
    exact ⟨n, fun m _ => H _ (Set.mem_range_self _)⟩
  · rw [WellFoundedGT, isWellFounded_iff, RelEmbedding.wellFounded_iff_isEmpty]
    refine ⟨fun a => ?_⟩
    obtain ⟨n, hn⟩ := h (a.swap : _ →r _).toOrderHom
    exact hn n.succ n.lt_succ_self.le ((RelEmbedding.map_rel_iff _).2 n.lt_succ_self)
/-
**WellFoundedGT.monotone_chain_condition'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedGT.monotone_chain_condition' [Preorder α] [h : WellFoundedGT α]
 (a : Nat ->o α) : exists n, forall m, n <= m -> ¬a n < a m
参数：a : Nat ->o α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `wellFoundedGT_iff_monotone_chain_condition'`：wellFoundedGT_iff_monotone_
chain_condition' [Preorder α] : WellFoundedGT α ↔ forall a : Nat ->o α, exists n
, forall m, n <= m -> ¬a n < a m
-/
theorem WellFoundedGT.monotone_chain_condition' [Preorder α] [h : WellFoundedGT α] (a : ℕ →o α) :
    ∃ n, ∀ m, n ≤ m → ¬a n < a m :=
  wellFoundedGT_iff_monotone_chain_condition'.1 h a

/-- A stronger version of the **monotone chain** condition for partial orders.

See `wellFoundedGT_iff_monotone_chain_condition'` for a version on preorders. -/
/-
**wellFoundedGT_iff_monotone_chain_condition** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellFoundedGT_iff_monotone_chain_condition [PartialOrder α] : WellFoundedG
T α ↔ forall a : Nat ->o α, exists n, forall m, n <= m -> a n = a m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `wellFoundedGT_iff_monotone_chain_condition'`：wellFoundedGT_iff_monotone_
chain_condition' [Preorder α] : WellFoundedGT α ↔ forall a : Nat ->o α, exists n
, forall m, n <= m -> ¬a n < a m
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A stronger version of the **monotone chain** condition for partial orders.

See `wellFoundedGT_iff_monotone_chain_condition'` for a version on preorders.
-/
theorem wellFoundedGT_iff_monotone_chain_condition [PartialOrder α] :
    WellFoundedGT α ↔ ∀ a : ℕ →o α, ∃ n, ∀ m, n ≤ m → a n = a m :=
  wellFoundedGT_iff_monotone_chain_condition'.trans <| by
  congrm ∀ a, ∃ n, ∀ m h, ?_
  rw [lt_iff_le_and_ne]
  simp [a.mono h]
/-
**WellFoundedGT.monotone_chain_condition** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedGT.monotone_chain_condition [PartialOrder α] [h : WellFoundedGT
 α] (a : Nat ->o α) : exists n, forall m, n <= m -> a n = a m
参数：a : Nat ->o α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `wellFoundedGT_iff_monotone_chain_condition`：wellFoundedGT_iff_monotone_c
hain_condition [PartialOrder α] : WellFoundedGT α ↔ forall a : Nat ->o α, exists
 n, forall m, n <= m -> a n = a …
-/
theorem WellFoundedGT.monotone_chain_condition [PartialOrder α] [h : WellFoundedGT α] (a : ℕ →o α) :
    ∃ n, ∀ m, n ≤ m → a n = a m :=
  wellFoundedGT_iff_monotone_chain_condition.1 h a

/-- The **antitone chain** condition: an antitone sequence in a partially-ordered type with
well-founded `<` is eventually constant.

This is the dual of `WellFoundedGT.monotone_chain_condition`. It is provided for convenience,
since it unbundles the antitone property from the order homomorphism. -/
/-
**WellFoundedLT.antitone_chain_condition** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedLT.antitone_chain_condition [PartialOrder α] [WellFoundedLT α] 
{f : Nat -> α} (hf : Antitone f) : exists n, forall m, n <= m -> f n = f m
参数：hf : Antitone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedGT.monotone_chain_condition`：WellFoundedGT.monotone_chain_con
dition [PartialOrder α] [h : WellFoundedGT α] (a : Nat ->o α) : exists n, forall
 m, n <= m -> a n = a m
· 使用定理 `instWellFoundedGTOrderDualOfWellFoundedLT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedLT α], WellFoundedGT αᵒᵈ

--- 原说明 ---
The **antitone chain** condition: an antitone sequence in a partially-ordered ty
pe with
well-founded `<` is eventually constant.

This is the dual of `WellFoundedGT.monotone_chain_condition`. It is provided for
 convenience,
since it unbundles the antitone property from the order homomorphism.
-/
theorem WellFoundedLT.antitone_chain_condition [PartialOrder α] [WellFoundedLT α]
    {f : ℕ → α} (hf : Antitone f) : ∃ n, ∀ m, n ≤ m → f n = f m :=
  WellFoundedGT.monotone_chain_condition ⟨OrderDual.toDual ∘ f, hf⟩

/-- Given an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a partially-ordered
type, `monotonicSequenceLimitIndex a` is the least natural number `n` for which `aₙ` reaches the
constant value. For sequences that are not eventually constant, `monotonicSequenceLimitIndex a`
is defined, but is a junk value. -/
/-
**monotonicSequenceLimitIndex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：monotonicSequenceLimitIndex [Preorder α] (a : Nat ->o α) : Nat
参数：a : Nat ->o α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a partial
ly-ordered
type, `monotonicSequenceLimitIndex a` is the least natural number `n` for which 
`aₙ` reaches the
constant value. For sequences that are not eventually constant, `monotonicSequen
ceLimitIndex a`
is defined, but is a junk value.
-/
noncomputable def monotonicSequenceLimitIndex [Preorder α] (a : ℕ →o α) : ℕ :=
  sInf { n | ∀ m, n ≤ m → a n = a m }

/-- The constant value of an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a
partially-ordered type. -/
/-
**monotonicSequenceLimit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：monotonicSequenceLimit [Preorder α] (a : Nat ->o α)
参数：a : Nat ->o α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant value of an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ .
..` in a
partially-ordered type.
-/
noncomputable def monotonicSequenceLimit [Preorder α] (a : ℕ →o α) :=
  a (monotonicSequenceLimitIndex a)
/-
**le_monotonicSequenceLimit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_monotonicSequenceLimit [PartialOrder α] [WellFoundedGT α] (a : Nat ->o 
α) (m : Nat) : a m <= monotonicSequenceLimit a
参数：a : Nat ->o α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Nat.sInf_mem`：sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s
· 使用定理 `WellFoundedGT.monotone_chain_condition`：WellFoundedGT.monotone_chain_con
dition [PartialOrder α] [h : WellFoundedGT α] (a : Nat ->o α) : exists n, forall
 m, n <= m -> a n = a m
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem le_monotonicSequenceLimit [PartialOrder α] [WellFoundedGT α] (a : ℕ →o α) (m : ℕ) :
    a m ≤ monotonicSequenceLimit a := by
  rcases le_or_gt m (monotonicSequenceLimitIndex a) with hm | hm
  · exact a.monotone hm
  · obtain h := WellFoundedGT.monotone_chain_condition a
    exact (Nat.sInf_mem (s := {n | ∀ m, n ≤ m → a n = a m}) h m hm.le).ge
/-
**WellFoundedGT.iSup_eq_monotonicSequenceLimit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedGT.iSup_eq_monotonicSequenceLimit [CompleteLattice α] [WellFoun
dedGT α] (a : Nat ->o α) : iSup a = monotonicSequenceLimit a
参数：a : Nat ->o α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_monotonicSequenceLimit`：le_monotonicSequenceLimit [PartialOrder α] [W
ellFoundedGT α] (a : Nat ->o α) (m : Nat) : a m <= monotonicSequenceLimit a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem WellFoundedGT.iSup_eq_monotonicSequenceLimit [CompleteLattice α]
    [WellFoundedGT α] (a : ℕ →o α) : iSup a = monotonicSequenceLimit a :=
  (iSup_le (le_monotonicSequenceLimit a)).antisymm (le_iSup a _)
/-
**WellFoundedGT.ciSup_eq_monotonicSequenceLimit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedGT.ciSup_eq_monotonicSequenceLimit [ConditionallyCompleteLattic
e α] [WellFoundedGT α] (a : Nat ->o α) (ha : BddAbove (Set.range a)) : iSup a = 
monotonicSequenceLimit a
参数：a : Nat ->o α；ha : BddAbove (Set.range a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `le_monotonicSequenceLimit`：le_monotonicSequenceLimit [PartialOrder α] [W
ellFoundedGT α] (a : Nat ->o α) (m : Nat) : a m <= monotonicSequenceLimit a
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
-/
theorem WellFoundedGT.ciSup_eq_monotonicSequenceLimit [ConditionallyCompleteLattice α]
    [WellFoundedGT α] (a : ℕ →o α) (ha : BddAbove (Set.range a)) :
    iSup a = monotonicSequenceLimit a :=
  (ciSup_le (le_monotonicSequenceLimit a)).antisymm (le_ciSup ha _)
/-
**exists_covBy_seq_of_wellFoundedLT_wellFoundedGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (α) [Preorder α] [Nonempty
 α] [wfl : WellFoundedLT α] [wfg : WellFoundedGT α] : exists a : Nat -> α, IsMin
 (a 0) ∧ exists n, IsMax (a n) ∧ forall i < n, a i ⋖ a (i + 1)
参数：α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nonempty_iff_univ_nonempty`：nonempty_iff_univ_nonempty : Nonempty α 
↔ (univ : Set α).Nonempty
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isMin_iff_forall_not_lt`：isMin_iff_forall_not_lt : IsMin a ↔ forall b, ¬
b < a
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `RelEmbedding.not_wellFounded`：not_wellFounded (f : ((· > ·) : Nat -> Nat
 -> Prop) ↪r r) : ¬WellFounded r
· 使用定理 `instIsStrictOrderGt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x2 < x1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
· 使用引理 `exists_covBy_of_wellFoundedLT`：exists_covBy_of_wellFoundedLT [wf : WellF
oundedLT α] ⦃a : α⦄ (h : ¬ IsMax a) : exists a', a ⋖ a'
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (α) [Preorder α]
    [Nonempty α] [wfl : WellFoundedLT α] [wfg : WellFoundedGT α] :
    ∃ a : ℕ → α, IsMin (a 0) ∧ ∃ n, IsMax (a n) ∧ ∀ i < n, a i ⋖ a (i + 1) := by
  choose next hnext using exists_covBy_of_wellFoundedLT (α := α)
  have hα := Set.nonempty_iff_univ_nonempty.mp ‹_›
  classical
  let a : ℕ → α := Nat.rec (wfl.wf.min _ hα) fun _n a ↦ if ha : IsMax a then a else next ha
  refine ⟨a, isMin_iff_forall_not_lt.mpr fun _ ↦ wfl.wf.not_lt_min _ (Set.mem_univ _), ?_⟩
  have cov n (hn : ¬ IsMax (a n)) : a n ⋖ a (n + 1) := by
    change a n ⋖ if ha : IsMax (a n) then a n else _
    rw [dif_neg hn]
    exact hnext hn
  have H : ∃ n, IsMax (a n) := by
    by_contra!
    exact (RelEmbedding.natGT a fun n ↦ (cov n (this n)).1).not_wellFounded wfg.wf
  exact ⟨_, wellFounded_lt.min_mem _ H, fun i h ↦ cov _ (wellFounded_lt.not_lt_min _ · h)⟩
/-
**exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le {α : Type*} [Partial
Order α] [wfl : WellFoundedLT α] [wfg : WellFoundedGT α] {x y : α} (h : x <= y) 
: exists a : Nat -> α, a 0 = x ∧ exists n, a n = y ∧ forall i < n, a i ⋖ a (i + 
1)
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `exists_covBy_seq_of_wellFoundedLT_wellFoundedGT`：exists_covBy_seq_of_wel
lFoundedLT_wellFoundedGT (α) [Preorder α] [Nonempty α] [wfl : WellFoundedLT α] [
wfg : WellFoundedGT α] : exists a : N…
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le {α : Type*} [PartialOrder α]
    [wfl : WellFoundedLT α] [wfg : WellFoundedGT α] {x y : α} (h : x ≤ y) :
    ∃ a : ℕ → α, a 0 = x ∧ ∃ n, a n = y ∧ ∀ i < n, a i ⋖ a (i + 1) := by
  let S := Set.Icc x y
  let hS : BoundedOrder S :=
    { top := ⟨y, h, le_rfl⟩, le_top x := x.2.2, bot := ⟨x, le_rfl, h⟩, bot_le x := x.2.1 }
  obtain ⟨a, h₁, n, h₂, e⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT S
  simp only [isMin_iff_eq_bot, Subtype.ext_iff, isMax_iff_eq_top] at h₁ h₂
  exact ⟨Subtype.val ∘ a, h₁, n, h₂, fun i hi ↦ ⟨(e i hi).1, fun c hc h ↦ (e i hi).2
    (c := ⟨c, (a i).2.1.trans hc.le, h.le.trans (a _).2.2⟩) hc h⟩⟩
