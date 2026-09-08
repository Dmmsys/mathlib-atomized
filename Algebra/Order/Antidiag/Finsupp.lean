/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Eric Wieser, Bhavik Mehta,
  Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Antidiagonal of finitely supported functions as finsets

This file defines the finset of finitely functions summing to a specific value on a finset. Such
finsets should be thought of as the "antidiagonals" in the space of finitely supported functions.

Precisely, for a commutative monoid `μ` with antidiagonals (see `Finset.HasAntidiagonal`),
`Finset.finsuppAntidiag s n` is the finset of all finitely supported functions `f : ι →₀ μ` with
support contained in `s` and such that the sum of its values equals `n : μ`.

We define it using `Finset.piAntidiag s n`, the corresponding antidiagonal in `ι → μ`.

## Main declarations

* `Finset.finsuppAntidiag s n`: Finset of all finitely supported functions `f : ι →₀ μ` with support
  contained in `s` and such that the sum of its values equals `n : μ`.

-/

@[expose] public section

assert_not_exists Field

open Finsupp Function

variable {ι μ μ' : Type*}

namespace Finset
section AddCommMonoid
variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ} {f : ι →₀ μ}

/-- The finset of functions `ι →₀ μ` with support contained in `s` and sum equal to `n`. -/
/-
**Finset.finsuppAntidiag** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：finsuppAntidiag (s : Finset ι) (n : μ) : Finset (ι ->₀ μ)
参数：s : Finset ι；n : μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finset of functions `ι →₀ μ` with support contained in `s` and sum equal to 
`n`.
-/
def finsuppAntidiag (s : Finset ι) (n : μ) : Finset (ι →₀ μ) :=
  (piAntidiag s n).attach.map ⟨fun f ↦ ⟨s.filter (f.1 · ≠ 0), f.1, by
    simpa using (mem_piAntidiag.1 f.2).2⟩, fun _ _ hfg ↦ Subtype.ext (congr_arg (⇑) hfg)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.mem_finsuppAntidiag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {μ : Type u_2} [inst : DecidableEq ι] [inst_1 : AddCommMo
noid μ] [inst_2 : Finset.HasAntidiagonal μ]   [inst_3 : DecidableEq μ] {s : Fins
et ι} {n : μ} {f : ι →₀ μ}, f ∈ s.finsuppAntidiag n ↔ s.sum ⇑f = n ∧ f.support ⊆
 s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.mk.congr_simp`：∀ {α : Type u_9} {M : Type u_10} [inst : Zero M] 
(support support_1 : Finset α) (e_support : support = support_1)   (toFun toFun_
1 : α → M) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun
 toFun_1 : α → β) (e_toFun : toFun = toFun_1) (inj' : Function.Injective toFun),
   { toFun := toFun, i…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_finsuppAntidiag : f ∈ finsuppAntidiag s n ↔ s.sum f = n ∧ f.support ⊆ s := by
  simp [finsuppAntidiag, ← DFunLike.coe_fn_eq, subset_iff]
/-
**Finset.mem_finsuppAntidiag'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_finsuppAntidiag' : f in finsuppAntidiag s n ↔ f.sum (fun _ x => x) = n
 ∧ f.support subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_finsuppAntidiag' :
    f ∈ finsuppAntidiag s n ↔ f.sum (fun _ x ↦ x) = n ∧ f.support ⊆ s := by
  simp only [mem_finsuppAntidiag, and_congr_left_iff]
  rintro hf
  rw [sum_of_support_subset (N := μ) f hf (fun _ x ↦ x) fun _ _ ↦ rfl]
/-
**Finset.finsuppAntidiag_empty_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {μ : Type u_2} [inst : DecidableEq ι] [inst_1 : AddCommMo
noid μ] [inst_2 : Finset.HasAntidiagonal μ]   [inst_3 : DecidableEq μ], ∅.finsup
pAntidiag 0 = {0}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma finsuppAntidiag_empty_zero : finsuppAntidiag (∅ : Finset ι) (0 : μ) = {0} := by
  ext f; simp
/-
**Finset.finsuppAntidiag_empty_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {μ : Type u_2} [inst : DecidableEq ι] [inst_1 : AddCommMo
noid μ] [inst_2 : Finset.HasAntidiagonal μ]   [inst_3 : DecidableEq μ] {n : μ}, 
n ≠ 0 → ∅.finsuppAntidiag n = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem {s : Finset 
α} (H : forall x, x ∉ s) : s = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma finsuppAntidiag_empty_of_ne_zero (hn : n ≠ 0) :
    finsuppAntidiag (∅ : Finset ι) n = ∅ :=
  eq_empty_of_forall_notMem (by simp [hn.symm])
/-
**Finset.finsuppAntidiag_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：finsuppAntidiag_empty (n : μ) : finsuppAntidiag (∅ : Finset ι) n = if n = 
0 then {0} else ∅
参数：n : μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.finsuppAntidiag_empty_zero`：∀ {ι : Type u_1} {μ : Type u_2} [inst
 : DecidableEq ι] [inst_1 : AddCommMonoid μ] [inst_2 : Finset.HasAntidiagonal μ]
   [inst_3 : DecidableE…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.finsuppAntidiag_empty_of_ne_zero`：∀ {ι : Type u_1} {μ : Type u_2}
 [inst : DecidableEq ι] [inst_1 : AddCommMonoid μ] [inst_2 : Finset.HasAntidiago
nal μ]   [inst_3 : DecidableE…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma finsuppAntidiag_empty (n : μ) :
    finsuppAntidiag (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by split_ifs with hn <;> simp [*]
/-
**Finset.mem_finsuppAntidiag_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_finsuppAntidiag_insert {a : ι} {s : Finset ι} (h : a ∉ s) (n : μ) {f :
 ι ->₀ μ} : f in finsuppAntidiag (insert a s) n ↔ exists m in antidiagonal n, ex
ists (g : ι ->₀ μ), f = Finsupp.update g a m.1 ∧ g in finsuppAntidiag s m.2
参数：h : a ∉ s；n : μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.update_erase_eq_update`：∀ {α : Type u_1} {M : Type u_5} [inst : 
Zero M] (f : α →₀ M) (a : α) (b : M),   (Finsupp.erase a f).update a b = f.updat
e a b
· 使用定理 `Finsupp.update_self`：update_self : f.update a (f a) = f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.erase_ne`：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.e
rase a) a' = f a'
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Finsupp.support_erase`：support_erase [DecidableEq α] {a : α} {f : α ->₀ 
M} : (f.erase a).support = f.support.erase a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.subset_insert_iff`：subset_insert_iff {a : α} {s t : Finset α} : s
 subseteq insert a t ↔ s.erase a subseteq t
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finsupp.support_update_subset`：support_update_subset [DecidableEq α] : s
upport (f.update a b) subseteq insert a f.support
· 使用定理 `Finset.insert_subset_insert`：insert_subset_insert (a : α) {s t : Finset 
α} (h : s subseteq t) : insert a s subseteq insert a t
-/
theorem mem_finsuppAntidiag_insert {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) {f : ι →₀ μ} :
    f ∈ finsuppAntidiag (insert a s) n ↔
      ∃ m ∈ antidiagonal n, ∃ (g : ι →₀ μ),
        f = Finsupp.update g a m.1 ∧ g ∈ finsuppAntidiag s m.2 := by
  simp only [mem_finsuppAntidiag, mem_antidiagonal, Prod.exists, sum_insert h]
  constructor
  · rintro ⟨rfl, hsupp⟩
    refine ⟨_, _, rfl, Finsupp.erase a f, ?_, ?_, ?_⟩
    · rw [update_erase_eq_update, Finsupp.update_self]
    · apply sum_congr rfl
      intro x hx
      rw [Finsupp.erase_ne (ne_of_mem_of_not_mem hx h)]
    · rwa [support_erase, ← subset_insert_iff]
  · rintro ⟨n1, n2, rfl, g, rfl, rfl, hgsupp⟩
    refine ⟨?_, (support_update_subset _ _).trans (insert_subset_insert a hgsupp)⟩
    simp only [coe_update]
    apply congr_arg₂
    · rw [Function.update_self]
    · apply sum_congr rfl
      intro x hx
      rw [update_of_ne (ne_of_mem_of_not_mem hx h) n1 ⇑g]

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.finsuppAntidiag_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：finsuppAntidiag_insert {a : ι} {s : Finset ι} (h : a ∉ s) (n : μ) : finsup
pAntidiag (insert a s) n = (antidiagonal n).biUnion (fun p : μ × μ => (finsuppAn
tidiag s p.snd).attach.map ⟨fun f => Finsupp.update f.val a p.fst, (fun ⟨f, hf⟩ 
⟨g, hg⟩ hfg => Subtype.ext <| by simp only [mem_finsuppAntidiag] at hf hg simp o
nly [DFunLike.ext_iff] at hfg ⊢ intro x obtain rfl | hx
参数：h : a ∉ s；n : μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_finsuppAntidiag_insert`：mem_finsuppAntidiag_insert {a : ι} {s
 : Finset ι} (h : a ∉ s) (n : μ) {f : ι ->₀ μ} : f in finsuppAntidiag (insert a 
s) n ↔ exists m in anti…
· 使用定理 `Finset.mem_biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : 
α → Finset β} [inst : DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t
 a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finsuppAntidiag_insert {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) :
    finsuppAntidiag (insert a s) n = (antidiagonal n).biUnion
      (fun p : μ × μ =>
        (finsuppAntidiag s p.snd).attach.map
        ⟨fun f => Finsupp.update f.val a p.fst,
        (fun ⟨f, hf⟩ ⟨g, hg⟩ hfg => Subtype.ext <| by
          simp only [mem_finsuppAntidiag] at hf hg
          simp only [DFunLike.ext_iff] at hfg ⊢
          intro x
          obtain rfl | hx := eq_or_ne x a
          · replace hf := mt (hf.2 ·) h
            replace hg := mt (hg.2 ·) h
            rw [notMem_support_iff.mp hf, notMem_support_iff.mp hg]
          · simpa only [coe_update, Function.update, dif_neg hx] using hfg x)⟩) := by
  ext f
  rw [mem_finsuppAntidiag_insert h, mem_biUnion]
  simp_rw [mem_map, mem_attach, true_and, Subtype.exists, Embedding.coeFn_mk, exists_prop, and_comm,
    eq_comm]

@[gcongr]
/-
**Finset.finsuppAntidiag_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：finsuppAntidiag_mono {s t : Finset ι} (h : s subseteq t) (n : μ) : finsupp
Antidiag s n subseteq finsuppAntidiag t n
参数：h : s subseteq t；n : μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem finsuppAntidiag_mono {s t : Finset ι} (h : s ⊆ t) (n : μ) :
    finsuppAntidiag s n ⊆ finsuppAntidiag t n := by
  intro a
  simp_rw [mem_finsuppAntidiag']
  rintro ⟨hsum, hmem⟩
  exact ⟨hsum, hmem.trans h⟩

variable [AddCommMonoid μ'] [HasAntidiagonal μ'] [DecidableEq μ']

set_option backward.isDefEq.respectTransparency false in
-- This should work under the assumption that e is an embedding and an AddHom
/-
**Finset.mapRange_finsuppAntidiag_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mapRange_finsuppAntidiag_subset {e : μ ≃+ μ'} {s : Finset ι} {n : μ} : (fi
nsuppAntidiag s n).map (mapRange.addEquiv e).toEmbedding subseteq finsuppAntidia
g s (e n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddEquiv.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZeroClass 
M] [inst_1 : AddZeroClass N] (h : M ≃+ N), h 0 = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.mapRange.equiv_apply`：∀ {ι : Type u_3} {M : Type u_4} {N : Type 
u_5} [inst : Zero M] [inst_1 : Zero N] (e : M ≃ N) (hf : e 0 = 0)   (g : ι →₀ M)
, (Finsupp.mapRang…
· 使用定理 `Finsupp.sum_mapRange_index`：∀ {α : Type u_1} {M : Type u_8} {M' : Type u
_9} {N : Type u_10} [inst : Zero M] [inst_1 : Zero M']   [inst_2 : AddCommMonoid
 N] {f : M → M'}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Finsupp.support_mapRange`：support_mapRange {f : M -> N} {hf : f 0 = 0} {
g : α ->₀ M} : (mapRange f hf g).support subseteq g.support
-/
lemma mapRange_finsuppAntidiag_subset {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (finsuppAntidiag s n).map (mapRange.addEquiv e).toEmbedding ⊆ finsuppAntidiag s (e n) := by
  intro f
  simp only [mem_map, mem_finsuppAntidiag']
  rintro ⟨g, ⟨hsum, hsupp⟩, rfl⟩
  simp only [AddEquiv.toEquiv_eq_coe, mapRange.addEquiv_toEquiv, Equiv.coe_toEmbedding,
    mapRange.equiv_apply, EquivLike.coe_coe]
  constructor
  · rw [sum_mapRange_index (fun _ ↦ rfl), ← hsum, _root_.map_finsuppSum]
  · exact subset_trans (support_mapRange) hsupp
/-
**Finset.mapRange_finsuppAntidiag_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mapRange_finsuppAntidiag_eq {e : μ ≃+ μ'} {s : Finset ι} {n : μ} : (finsup
pAntidiag s n).map (mapRange.addEquiv e).toEmbedding = finsuppAntidiag s (e n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用引理 `Finset.mapRange_finsuppAntidiag_subset`：mapRange_finsuppAntidiag_subset 
{e : μ ≃+ μ'} {s : Finset ι} {n : μ} : (finsuppAntidiag s n).map (mapRange.addEq
uiv e).toEmbedding subseteq …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddEquiv.eq_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [
inst_1 : Add N] (e : M ≃+ N) {x : N} {y : M}, y = e.symm x ↔ e y = x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.mem_map_equiv`：mem_map_equiv {f : α ≃ β} {b : β} : b in s.map f.t
oEmbedding ↔ f.symm b in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
· 使用定理 `Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding`：equiv_symm_
toEmbedding_trans_toEmbedding {α β : Sort*} (e : α ≃ β) : e.symm.toEmbedding.tra
ns e.toEmbedding = Embedding.refl _
· 使用定理 `Finset.map_refl`：map_refl : s.map (Embedding.refl _) = s
-/
lemma mapRange_finsuppAntidiag_eq {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (finsuppAntidiag s n).map (mapRange.addEquiv e).toEmbedding = finsuppAntidiag s (e n) := by
  ext f
  constructor
  · apply mapRange_finsuppAntidiag_subset
  · set h := (mapRange.addEquiv e).toEquiv with hh
    intro hf
    have : n = e.symm (e n) := (AddEquiv.eq_symm_apply e).mpr rfl
    rw [mem_map_equiv, this]
    apply mapRange_finsuppAntidiag_subset
    rw [← mem_map_equiv]
    convert! hf
    rw [map_map, hh]
    convert! map_refl
    apply Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding

end AddCommMonoid

section CanonicallyOrderedAddCommMonoid
variable [DecidableEq ι] [DecidableEq μ] [AddCommMonoid μ] [PartialOrder μ]
  [CanonicallyOrderedAdd μ] [HasAntidiagonal μ]

/-
**Finset.finsuppAntidiag_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {μ : Type u_2} [inst : DecidableEq ι] [inst_1 : Decidable
Eq μ] [inst_2 : AddCommMonoid μ]   [inst_3 : PartialOrder μ] [CanonicallyOrdered
Add μ] [inst_5 : Finset.HasAntidiagonal μ] (s : Finset ι),   s.finsuppAntidiag 0
 = {0}
参数：s : Finset ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.mk.congr_simp`：∀ {α : Type u_9} {M : Type u_10} [inst : Zero M] 
(support support_1 : Finset α) (e_support : support = support_1)   (toFun toFun_
1 : α → M) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun
 toFun_1 : α → β) (e_toFun : toFun = toFun_1) (inj' : Function.Injective toFun),
   { toFun := toFun, i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Finset.piAntidiag_zero`：∀ {ι : Type u_1} {μ : Type u_2} [inst : Decidabl
eEq ι] [inst_1 : AddCommMonoid μ] [inst_2 : PartialOrder μ]   [CanonicallyOrdere
dAdd μ] [ins…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma finsuppAntidiag_zero (s : Finset ι) : finsuppAntidiag s (0 : μ) = {0} := by
  ext f; simp [finsuppAntidiag, ← DFunLike.coe_fn_eq (g := f), eq_comm]

end CanonicallyOrderedAddCommMonoid
end Finset

