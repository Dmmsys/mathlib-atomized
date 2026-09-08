/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Algebra.Module.End

/-!
# Finite sums over modules over a ring
-/

public section

variable {ι κ α β R M : Type*}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-
**List.sum_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.sum_smul {l : List R} {x : M} : l.sum • x = (l.map fun r => r • x).su
m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem List.sum_smul {l : List R} {x : M} : l.sum • x = (l.map fun r ↦ r • x).sum :=
  map_list_sum ((smulAddHom R M).flip x) l
/-
**Multiset.sum_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.sum_smul {l : Multiset R} {x : M} : l.sum • x = (l.map fun r => r
 • x).sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_multiset_sum`：∀ {M : Type u_5} {N : Type u_6} [inst : A
ddCommMonoid M] [inst_1 : AddCommMonoid N] (f : M →+ N) (s : Multiset M),   f s.
sum = (Multiset.map…
-/
theorem Multiset.sum_smul {l : Multiset R} {x : M} : l.sum • x = (l.map fun r ↦ r • x).sum :=
  ((smulAddHom R M).flip x).map_multiset_sum l
/-
**Multiset.sum_smul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.sum_smul_sum {s : Multiset R} {t : Multiset M} : s.sum • t.sum = 
((s ×ˢ t).map fun p : R × M => p.fst • p.snd).sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.cons_product`：cons_product : (a ::ₘ s) ×ˢ t = map (Prod.mk a) t
 + s ×ˢ t
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.sum_add`：∀ {M : Type u_5} [inst : AddCommMonoid M] (s t : Multi
set M), (s + t).sum = s.sum + t.sum
-/
theorem Multiset.sum_smul_sum {s : Multiset R} {t : Multiset M} :
    s.sum • t.sum = ((s ×ˢ t).map fun p : R × M ↦ p.fst • p.snd).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [add_smul, ih, ← Multiset.smul_sum]
/-
**Finset.sum_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (∑ i in s, f i) • x 
= ∑ i in s, f i • x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem Finset.sum_smul {f : ι → R} {s : Finset ι} {x : M} :
    (∑ i ∈ s, f i) • x = ∑ i ∈ s, f i • x := map_sum ((smulAddHom R M).flip x) f s
/-
**Finset.sum_smul_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.sum_smul_sum (s : Finset α) (t : Finset β) {f : α -> R} {g : β -> M
} : (∑ i in s, f i) • ∑ j in t, g j = ∑ i in s, ∑ j in t, f i • g j
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Finset.sum_smul_sum (s : Finset α) (t : Finset β) {f : α → R} {g : β → M} :
    (∑ i ∈ s, f i) • ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i • g j := by
  simp_rw [sum_smul, ← smul_sum]
/-
**Fintype.sum_smul_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fintype.sum_smul_sum [Fintype α] [Fintype β] (f : α -> R) (g : β -> M) : (
∑ i, f i) • ∑ j, g j = ∑ i, ∑ j, f i • g j
参数：f : α -> R；g : β -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sum_smul_sum`：Finset.sum_smul_sum (s : Finset α) (t : Finset β) {
f : α -> R} {g : β -> M} : (∑ i in s, f i) • ∑ j in t, g j = ∑ i in s, ∑ j in t,
 f i • g …
-/
lemma Fintype.sum_smul_sum [Fintype α] [Fintype β] (f : α → R) (g : β → M) :
    (∑ i, f i) • ∑ j, g j = ∑ i, ∑ j, f i • g j := Finset.sum_smul_sum _ _

end AddCommMonoid

open Finset

/-
**Finset.cast_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.cast_card [NonAssocSemiring R] (s : Finset α) : (#s : R) = ∑ _ in s
, 1
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Nat.smul_one_eq_cast`：Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring
 R] (m : Nat) : m • (1 : R) = ↑m
-/
theorem Finset.cast_card [NonAssocSemiring R] (s : Finset α) : (#s : R) = ∑ _ ∈ s, 1 := by
  rw [Finset.sum_const, Nat.smul_one_eq_cast]

namespace Fintype
variable [DecidableEq ι] [Fintype ι] [AddCommMonoid α]

/-
**Fintype.sum_piFinset_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：sum_piFinset_apply (f : κ -> α) (s : Finset κ) (i : ι) : ∑ g in piFinset f
un _ : ι => s, f (g i) = #s ^ (card ι - 1) • ∑ b in s, f b
参数：f : κ -> α；s : Finset κ；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} {s : Fin
set ι} [inst : AddCommMonoid M] [inst_1 : DecidableEq κ]   (f : κ → M) (g : ι → 
κ), ∑…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Fintype.eval_image_piFinset_const`：eval_image_piFinset_const {β} [Decida
bleEq β] (t : Finset β) (a : α) : ((piFinset fun _i : α => t).image fun f => f a
) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Fintype.card_filter_piFinset_const`：card_filter_piFinset_const (s : Fins
et κ) (i : ι) (j : κ) : #{f in piFinset fun _ => s | f i = j} = if j in s then #
s ^ (card ι - 1) else 0
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → M),   (∑ i ∈ s, if i ∈ t
 then f …
· 使用定理 `Finset.inter_self`：inter_self (s : Finset α) : s inter s = s
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_piFinset_apply (f : κ → α) (s : Finset κ) (i : ι) :
    ∑ g ∈ piFinset fun _ : ι ↦ s, f (g i) = #s ^ (card ι - 1) • ∑ b ∈ s, f b := by
  classical
  rw [Finset.sum_comp]
  simp only [eval_image_piFinset_const, card_filter_piFinset_const s, ite_smul, zero_smul, smul_sum,
    Finset.sum_ite_mem, inter_self]

@[simp]
/-
**Fintype.sum_single_smul** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：sum_single_smul {R : Type*} [Semiring R] [Module R α] (f : ι -> α) (r : R)
 (i₀ : ι) : ∑ i, (Pi.single (M
参数：f : ι -> α；r : R；i₀ : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
lemma sum_single_smul
    {R : Type*} [Semiring R] [Module R α] (f : ι → α) (r : R) (i₀ : ι) :
    ∑ i, (Pi.single (M := fun _ ↦ R) i₀ r i) • f i = r • f i₀ := by
  rw [Finset.sum_eq_single i₀, Pi.single_eq_same] <;> aesop

end Fintype

