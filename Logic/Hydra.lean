/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Order.GameAdd

/-!
# Termination of a hydra game

This file deals with the following version of the hydra game: each head of the hydra is
labelled by an element in a type `α`, and when you cut off one head with label `a`, it
grows back an arbitrary but finite number of heads, all labelled by elements smaller than
`a` with respect to a well-founded relation `r` on `α`. We show that no matter how (in
what order) you choose cut off the heads, the game always terminates, i.e. all heads will
eventually be cut off (but of course it can last arbitrarily long, i.e. takes an
arbitrary finite number of steps).

This result is stated as the well-foundedness of the `CutExpand` relation defined in
this file: we model the heads of the hydra as a multiset of elements of `α`, and the
valid "moves" of the game are modelled by the relation `CutExpand r` on `Multiset α`:
`CutExpand r s' s` is true iff `s'` is obtained by removing one head `a ∈ s` and
adding back an arbitrary multiset `t` of heads such that all `a' ∈ t` satisfy `r a' a`.

We follow the proof by Peter LeFanu Lumsdaine at https://mathoverflow.net/a/229084/3332.

TODO: formalize the relations corresponding to more powerful (e.g. Kirby–Paris and Buchholz)
hydras, and prove their well-foundedness.
-/

@[expose] public section


namespace Relation

open Multiset Prod

variable {α : Type*}

/-- The relation that specifies valid moves in our hydra game. `CutExpand r s' s`
  means that `s'` is obtained by removing one head `a ∈ s` and adding back an arbitrary
  multiset `t` of heads such that all `a' ∈ t` satisfy `r a' a`.

  This is most directly translated into `s' = s.erase a + t`, but `Multiset.erase` requires
  `DecidableEq α`, so we use the equivalent condition `s' + {a} = s + t` instead, which
  is also easier to verify for explicit multisets `s'`, `s` and `t`.

  We also don't include the condition `a ∈ s` because `s' + {a} = s + t` already
  guarantees `a ∈ s + t`, and if `r` is irreflexive then `a ∉ t`, which is the
  case when `r` is well-founded, the case we are primarily interested in.

  The lemma `Relation.cutExpand_iff` below converts between this convenient definition
  and the direct translation when `r` is irreflexive. -/
/-
**Relation.CutExpand** 是 Mathlib 中的一个定义，位于命名空间 `Relation`。
形式化陈述：CutExpand (r : α -> α -> Prop) (s' s : Multiset α) : Prop
参数：r : α -> α -> Prop；s' s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation that specifies valid moves in our hydra game. `CutExpand r s' s`
  means that `s'` is obtained by removing one head `a ∈ s` and adding back an ar
bitrary
  multiset `t` of heads such that all `a' ∈ t` satisfy `r a' a`.

  This is most directly translated into `s' = s.erase a + t`, but `Multiset.eras
e` requires
  `DecidableEq α`, so we use the equivalent condition `s' + {a} = s + t` instead
, which
  is also easier to verify for explicit multisets `s'`, `s` and `t`.

  We also don't include the condition `a ∈ s` because `s' + {a} = s + t` already
  guarantees `a ∈ s + t`, and if `r` is irreflexive then `a ∉ t`, which is the
  case when `r` is well-founded, the case we are primarily interested in.

  The lemma `Relation.cutExpand_iff` below converts between this convenient defi
nition
  and the direct translation when `r` is irreflexive.
-/
def CutExpand (r : α → α → Prop) (s' s : Multiset α) : Prop :=
  ∃ (t : Multiset α) (a : α), (∀ a' ∈ t, r a' a) ∧ s' + {a} = s + t

variable {r : α → α → Prop}
/-
**Relation.cutExpand_le_invImage_lex** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：cutExpand_le_invImage_lex [DecidableEq α] [Std.Irrefl r] : CutExpand r <= 
InvImage (Finsupp.Lex (rᶜ ⊓ (· != ·)) (· < ·)) toFinsupp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `Multiset.count_singleton`：count_singleton (a b : α) : count a ({b} : Mul
tiset α) = if a = b then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.count_eq_zero`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Mul
tiset α} {a : α}, Multiset.count a s = 0 ↔ a ∉ s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Multiset.count_singleton_self`：count_singleton_self (a : α) : count a ({
a} : Multiset α) = 1
· 使用定理 `irrefl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Irrefl r] (a : α), ¬
r a a
-/
theorem cutExpand_le_invImage_lex [DecidableEq α] [Std.Irrefl r] :
    CutExpand r ≤ InvImage (Finsupp.Lex (rᶜ ⊓ (· ≠ ·)) (· < ·)) toFinsupp := by
  rintro s t ⟨u, a, hr, he⟩
  replace hr := fun a' ↦ mt (hr a')
  refine ⟨a, fun b h ↦ ?_, ?_⟩ <;> simp_rw [toFinsupp_apply]
  · apply_fun count b at he
    simpa only [count_add, count_singleton, if_neg h.2, add_zero, count_eq_zero.2 (hr b h.1)]
      using he
  · apply_fun count a at he
    simp only [count_add, count_singleton_self, count_eq_zero.2 (hr _ (irrefl_of r a)),
      add_zero] at he
    exact he ▸ Nat.lt_succ_self _
/-
**Relation.cutExpand_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：cutExpand_singleton {s x} (h : forall x' in s, r x' x) : CutExpand r s {x}
参数：h : forall x' in s, r x' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem cutExpand_singleton {s x} (h : ∀ x' ∈ s, r x' x) : CutExpand r s {x} :=
  ⟨s, x, h, add_comm s _⟩
/-
**Relation.cutExpand_singleton_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：cutExpand_singleton_singleton {x' x} (h : r x' x) : CutExpand r {x'} {x}
参数：h : r x' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.cutExpand_singleton`：cutExpand_singleton {s x} (h : forall x' i
n s, r x' x) : CutExpand r s {x}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Multiset α
) ↔ b = a
-/
theorem cutExpand_singleton_singleton {x' x} (h : r x' x) : CutExpand r {x'} {x} :=
  cutExpand_singleton fun a h ↦ by rwa [mem_singleton.1 h]
/-
**Relation.cutExpand_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：cutExpand_add_left {t u} (s) : CutExpand r (s + t) (s + u) ↔ CutExpand r t
 u
参数：s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∃ a b, p a b) ↔ ∃ a b, q a b
)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_left_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 {a b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
-/
theorem cutExpand_add_left {t u} (s) : CutExpand r (s + t) (s + u) ↔ CutExpand r t u :=
  exists₂_congr fun _ _ ↦ and_congr Iff.rfl <| by rw [add_assoc, add_assoc, add_left_cancel_iff]
/-
**Relation.cutExpand_add_right** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：cutExpand_add_right {s' s} (t) : CutExpand r (s' + t) (s + t) ↔ CutExpand 
r s' s
参数：t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Relation.cutExpand_add_left`：cutExpand_add_left {t u} (s) : CutExpand r 
(s + t) (s + u) ↔ CutExpand r t u
-/
lemma cutExpand_add_right {s' s} (t) : CutExpand r (s' + t) (s + t) ↔ CutExpand r s' s := by
  convert! cutExpand_add_left t using 2 <;> apply add_comm
/-
**Relation.cutExpand_add_single** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：cutExpand_add_single {a' a : α} (s : Multiset α) (h : r a' a) : CutExpand 
r (s + {a'}) (s + {a})
参数：s : Multiset α；h : r a' a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Relation.cutExpand_add_left`：cutExpand_add_left {t u} (s) : CutExpand r 
(s + t) (s + u) ↔ CutExpand r t u
· 使用定理 `Relation.cutExpand_singleton_singleton`：cutExpand_singleton_singleton {x
' x} (h : r x' x) : CutExpand r {x'} {x}
-/
theorem cutExpand_add_single {a' a : α} (s : Multiset α) (h : r a' a) :
    CutExpand r (s + {a'}) (s + {a}) :=
  (cutExpand_add_left s).2 <| cutExpand_singleton_singleton h
/-
**Relation.cutExpand_single_add** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：cutExpand_single_add {a' a : α} (h : r a' a) (s : Multiset α) : CutExpand 
r ({a'} + s) ({a} + s)
参数：h : r a' a；s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Relation.cutExpand_add_right`：cutExpand_add_right {s' s} (t) : CutExpand
 r (s' + t) (s + t) ↔ CutExpand r s' s
· 使用定理 `Relation.cutExpand_singleton_singleton`：cutExpand_singleton_singleton {x
' x} (h : r x' x) : CutExpand r {x'} {x}
-/
theorem cutExpand_single_add {a' a : α} (h : r a' a) (s : Multiset α) :
    CutExpand r ({a'} + s) ({a} + s) :=
  (cutExpand_add_right s).2 <| cutExpand_singleton_singleton h
/-
**Relation.cutExpand_iff** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：cutExpand_iff [DecidableEq α] [Std.Irrefl r] {s' s : Multiset α} : CutExpa
nd r s' s ↔ exists (t : Multiset α) (a : α), (forall a' in t, r a' a) ∧ a in s ∧
 s' = s.erase a + t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∃ a b, p a b) ↔ ∃ a b, q a b
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_add`：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in
 s ∨ a in t
· 使用定理 `Multiset.erase_add_left_pos`：erase_add_left_pos {a : α} {s : Multiset α}
 (t) : a in s -> (s + t).erase a = s.erase a + t
· 使用引理 `irrefl`：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem cutExpand_iff [DecidableEq α] [Std.Irrefl r] {s' s : Multiset α} :
    CutExpand r s' s ↔
      ∃ (t : Multiset α) (a : α), (∀ a' ∈ t, r a' a) ∧ a ∈ s ∧ s' = s.erase a + t := by
  simp_rw [CutExpand, add_singleton_eq_iff]
  refine exists₂_congr fun t a ↦ ⟨?_, ?_⟩
  · rintro ⟨ht, ha, rfl⟩
    obtain h | h := mem_add.1 ha
    exacts [⟨ht, h, erase_add_left_pos t h⟩, (@irrefl α r _ a (ht a h)).elim]
  · rintro ⟨ht, h, rfl⟩
    exact ⟨ht, mem_add.2 (Or.inl h), (erase_add_left_pos t h).symm⟩
/-
**Relation.not_cutExpand_zero** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：not_cutExpand_zero [Std.Irrefl r] (s) : ¬CutExpand r s 0
参数：s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Relation.cutExpand_iff`：cutExpand_iff [DecidableEq α] [Std.Irrefl r] {s'
 s : Multiset α} : CutExpand r s' s ↔ exists (t : Multiset α) (a : α), (forall a
' in t, r a'…
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem not_cutExpand_zero [Std.Irrefl r] (s) : ¬CutExpand r s 0 := by
  classical
  rw [cutExpand_iff]
  rintro ⟨_, _, _, ⟨⟩, _⟩
/-
**Relation.cutExpand_zero** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：cutExpand_zero {x} : CutExpand r 0 {x}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma cutExpand_zero {x} : CutExpand r 0 {x} := ⟨0, x, nofun, add_comm 0 _⟩

/-- For any relation `r` on `α`, multiset addition `Multiset α × Multiset α → Multiset α` is a
  fibration between the game sum of `CutExpand r` with itself and `CutExpand r` itself. -/
/-
**Relation.cutExpand_fibration** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：cutExpand_fibration (r : α -> α -> Prop) : Fibration (GameAdd (CutExpand r
) (CutExpand r)) (CutExpand r) fun s => s.1 + s.2
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.add_singleton_eq_iff`：add_singleton_eq_iff {s t : Multiset α} {
a : α} : s + {a} = t ↔ a in t ∧ s = t.erase a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.mem_add`：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in
 s ∨ a in t
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.singleton_add`：singleton_add (a : α) (s : Multiset α) : {a} + s
 = a ::ₘ s
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `Multiset.erase_add_left_pos`：erase_add_left_pos {a : α} {s : Multiset α}
 (t) : a in s -> (s + t).erase a = s.erase a + t
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Multiset.erase_add_right_pos`：erase_add_right_pos {a : α} (s) (h : a in 
t) : (s + t).erase a = s + t.erase a

--- 原说明 ---
For any relation `r` on `α`, multiset addition `Multiset α × Multiset α → Multis
et α` is a
  fibration between the game sum of `CutExpand r` with itself and `CutExpand r` 
itself.
-/
theorem cutExpand_fibration (r : α → α → Prop) :
    Fibration (GameAdd (CutExpand r) (CutExpand r)) (CutExpand r) fun s ↦ s.1 + s.2 := by
  rintro ⟨s₁, s₂⟩ s ⟨t, a, hr, he⟩; dsimp at he ⊢
  classical
  obtain ⟨ha, rfl⟩ := add_singleton_eq_iff.1 he
  rw [add_assoc, mem_add] at ha
  obtain h | h := ha
  · refine ⟨(s₁.erase a + t, s₂), GameAdd.fst ⟨t, a, hr, ?_⟩, ?_⟩
    · rw [add_comm, ← add_assoc, singleton_add, cons_erase h]
    · rw [add_assoc s₁, erase_add_left_pos _ h, add_right_comm, add_assoc]
  · refine ⟨(s₁, (s₂ + t).erase a), GameAdd.snd ⟨t, a, hr, ?_⟩, ?_⟩
    · rw [add_comm, singleton_add, cons_erase h]
    · rw [add_assoc, erase_add_right_pos _ h]

/-- `CutExpand` preserves leftward-closedness under a relation. -/
/-
**Relation.cutExpand_closed** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：cutExpand_closed [Std.Irrefl r] (p : α -> Prop) (h : forall {a' a}, r a' a
 -> p a -> p a') {s' s : Multiset α} : CutExpand r s' s -> (forall a in s, p a) 
-> forall a in s', p a
参数：p : α -> Prop；h : forall {a' a}, r a' a -> p a -> p a'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Relation.cutExpand_iff`：cutExpand_iff [DecidableEq α] [Std.Irrefl r] {s'
 s : Multiset α} : CutExpand r s' s ↔ exists (t : Multiset α) (a : α), (forall a
' in t, r a'…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_add`：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in
 s ∨ a in t
· 使用定理 `Multiset.mem_of_mem_erase`：mem_of_mem_erase {a b : α} {s : Multiset α} :
 a in s.erase b -> a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`CutExpand` preserves leftward-closedness under a relation.
-/
lemma cutExpand_closed [Std.Irrefl r] (p : α → Prop)
    (h : ∀ {a' a}, r a' a → p a → p a') {s' s : Multiset α} :
    CutExpand r s' s → (∀ a ∈ s, p a) → ∀ a ∈ s', p a := by
  classical
  rw [cutExpand_iff]
  rintro ⟨t, a, hr, ha, rfl⟩ hsp a' h'
  obtain (h' | h') := mem_add.1 h'
  exacts [hsp a' (mem_of_mem_erase h'), h (hr a' h') (hsp a ha)]
/-
**Relation.cutExpand_double** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：cutExpand_double {a a₁ a₂} (h₁ : r a₁ a) (h₂ : r a₂ a) : CutExpand r {a₁, 
a₂} {a}
参数：h₁ : r a₁ a；h₂ : r a₂ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.cutExpand_singleton`：cutExpand_singleton {s x} (h : forall x' i
n s, r x' x) : CutExpand r s {x}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma cutExpand_double {a a₁ a₂} (h₁ : r a₁ a) (h₂ : r a₂ a) : CutExpand r {a₁, a₂} {a} :=
  cutExpand_singleton <| by
    simp only [insert_eq_cons, mem_cons, mem_singleton, forall_eq_or_imp, forall_eq]
    tauto
/-
**Relation.cutExpand_pair_left** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：cutExpand_pair_left {a' a b} (hr : r a' a) : CutExpand r {a', b} {a, b}
参数：hr : r a' a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Relation.cutExpand_add_right`：cutExpand_add_right {s' s} (t) : CutExpand
 r (s' + t) (s + t) ↔ CutExpand r s' s
· 使用定理 `Relation.cutExpand_singleton_singleton`：cutExpand_singleton_singleton {x
' x} (h : r x' x) : CutExpand r {x'} {x}
-/
lemma cutExpand_pair_left {a' a b} (hr : r a' a) : CutExpand r {a', b} {a, b} :=
  (cutExpand_add_right {b}).2 (cutExpand_singleton_singleton hr)
/-
**Relation.cutExpand_pair_right** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：cutExpand_pair_right {a b' b} (hr : r b' b) : CutExpand r {a, b'} {a, b}
参数：hr : r b' b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Relation.cutExpand_add_left`：cutExpand_add_left {t u} (s) : CutExpand r 
(s + t) (s + u) ↔ CutExpand r t u
· 使用定理 `Relation.cutExpand_singleton_singleton`：cutExpand_singleton_singleton {x
' x} (h : r x' x) : CutExpand r {x'} {x}
-/
lemma cutExpand_pair_right {a b' b} (hr : r b' b) : CutExpand r {a, b'} {a, b} :=
  (cutExpand_add_left {a}).2 (cutExpand_singleton_singleton hr)
/-
**Relation.cutExpand_double_left** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：cutExpand_double_left {a a₁ a₂ b} (h₁ : r a₁ a) (h₂ : r a₂ a) : CutExpand 
r {a₁, a₂, b} {a, b}
参数：h₁ : r a₁ a；h₂ : r a₂ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Relation.cutExpand_add_right`：cutExpand_add_right {s' s} (t) : CutExpand
 r (s' + t) (s + t) ↔ CutExpand r s' s
· 使用引理 `Relation.cutExpand_double`：cutExpand_double {a a₁ a₂} (h₁ : r a₁ a) (h₂ 
: r a₂ a) : CutExpand r {a₁, a₂} {a}
-/
lemma cutExpand_double_left {a a₁ a₂ b} (h₁ : r a₁ a) (h₂ : r a₂ a) :
    CutExpand r {a₁, a₂, b} {a, b} :=
  (cutExpand_add_right {b}).2 (cutExpand_double h₁ h₂)

/-- A multiset is accessible under `CutExpand` if all its singleton subsets are,
  assuming `r` is irreflexive. -/
/-
**Relation.acc_of_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：acc_of_singleton [Std.Irrefl r] {s : Multiset α} (hs : forall a in s, Acc 
(CutExpand r) {a}) : Acc (CutExpand r) s
参数：hs : forall a in s, Acc (CutExpand r) {a}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `Relation.not_cutExpand_zero`：not_cutExpand_zero [Std.Irrefl r] (s) : ¬Cu
tExpand r s 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.singleton_add`：singleton_add (a : α) (s : Multiset α) : {a} + s
 = a ::ₘ s
· 使用定理 `Acc.of_fibration`：∀ {α : Type u_1} {β : Type u_2} {rα : α → α → Prop} {r
β : β → β → Prop} (f : α → β),   Relation.Fibration rα rβ f → ∀ {a : α}, Acc rα 
a → Ac…
· 使用定理 `Relation.cutExpand_fibration`：cutExpand_fibration (r : α -> α -> Prop) :
 Fibration (GameAdd (CutExpand r) (CutExpand r)) (CutExpand r) fun s => s.1 + s.
2
· 使用定理 `Acc.prod_gameAdd`：Acc.prod_gameAdd (ha : Acc rα a) (hb : Acc rβ b) : Acc
 (Prod.GameAdd rα rβ) (a, b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Multiset.forall_mem_cons`：forall_mem_cons {p : α -> Prop} {a : α} {s : M
ultiset α} : (forall x in a ::ₘ s, p x) ↔ p a ∧ forall x in s, p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A multiset is accessible under `CutExpand` if all its singleton subsets are,
  assuming `r` is irreflexive.
-/
theorem acc_of_singleton [Std.Irrefl r] {s : Multiset α} (hs : ∀ a ∈ s, Acc (CutExpand r) {a}) :
    Acc (CutExpand r) s := by
  induction s using Multiset.induction with
  | empty => exact Acc.intro 0 fun s h ↦ (not_cutExpand_zero s h).elim
  | cons a s ihs =>
    rw [← s.singleton_add a]
    rw [forall_mem_cons] at hs
    exact (hs.1.prod_gameAdd <| ihs fun a ha ↦ hs.2 a ha).of_fibration _ (cutExpand_fibration r)

/-- A singleton `{a}` is accessible under `CutExpand r` if `a` is accessible under `r`,
  assuming `r` is irreflexive. -/
/-
**Relation._root_.Acc.cutExpand** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A singleton `{a}` is accessible under `CutExpand r` if `a` is accessible under `
r`,
  assuming `r` is irreflexive.
-/
theorem _root_.Acc.cutExpand [Std.Irrefl r] {a : α} (hacc : Acc r a) : Acc (CutExpand r) {a} := by
  induction hacc with | _ a h ih
  refine Acc.intro _ fun s ↦ ?_
  classical
  simp only [cutExpand_iff, mem_singleton]
  rintro ⟨t, a, hr, rfl, rfl⟩
  refine acc_of_singleton fun a' ↦ ?_
  rw [erase_singleton, zero_add]
  exact ih a' ∘ hr a'

/-- `CutExpand r` is well-founded when `r` is. -/
/-
**Relation._root_.WellFounded.cutExpand** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CutExpand r` is well-founded when `r` is.
-/
theorem _root_.WellFounded.cutExpand (hr : WellFounded r) : WellFounded (CutExpand r) :=
  ⟨have := hr.irrefl; fun _ ↦ acc_of_singleton fun a _ ↦ (hr.apply a).cutExpand⟩
/-
**Relation.** 是 Mathlib 中的一个实例，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : IsWellFounded α r] : IsWellFounded _ (CutExpand r) :=
  ⟨h.wf.cutExpand⟩

end Relation

