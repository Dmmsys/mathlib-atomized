/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Order.WellFoundedSet

/-!
# Pointwise instances on `Submonoid`s and `AddSubmonoid`s

This file provides:

* `Submonoid.inv`
* `AddSubmonoid.neg`

and the actions

* `Submonoid.pointwiseMulAction`
* `AddSubmonoid.pointwiseAddAction`

which matches the action of `Set.mulActionSet`.

## Implementation notes

Most of the lemmas in this file are direct copies of lemmas from
`Mathlib/Algebra/Group/Pointwise/Set/Basic.lean` and
`Mathlib/Algebra/Group/Action/Pointwise/Set/Basic.lean`.
While the statements of these lemmas are defeq, we repeat them here due to them not being
syntactically equal. Before adding new lemmas here, consider if they would also apply to the action
on `Set`s.
-/

@[expose] public section

assert_not_exists GroupWithZero

open Set Pointwise

variable {α G M R A S : Type*}
variable [Monoid M] [AddMonoid A]

@[to_additive (attr := simp, norm_cast)]
/-
**coe_mul_coe** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_mul_coe [SetLike S M] [SubmonoidClass S M] (H : S) : H * H = (H : Set 
M)
参数：H : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma coe_mul_coe [SetLike S M] [SubmonoidClass S M] (H : S) : H * H = (H : Set M) := by
  aesop (add simp mem_mul)

@[to_additive]
/-
**Set.subtype_smul_set** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.subtype_smul_set {S α β : Type*} [SMul α β] [SetLike S α] {s : S} (x :
 s) (t : Set β) : (x • t : Set β) = (x : α) • t
参数：x : s；t : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Set.subtype_smul_set {S α β : Type*} [SMul α β] [SetLike S α] {s : S} (x : s) (t : Set β) :
    (x • t : Set β) = (x : α) • t :=
  rfl

@[to_additive (attr := simp)]
/-
**coe_set_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_3} {S : Type u_6} [inst : Monoid M] [inst_1 : SetLike S M] [
SubmonoidClass S M] {n : ℕ},   n ≠ 0 → ∀ (H : S), ↑H ^ n = ↑H
参数：H : S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_set_pow [SetLike S M] [SubmonoidClass S M] :
    ∀ {n} (_ : n ≠ 0) (H : S), (H ^ n : Set M) = H
  | 1, _, H => by simp
  | n + 2, _, H => by rw [pow_succ, coe_set_pow n.succ_ne_zero, coe_mul_coe]

/-! Some lemmas about pointwise multiplication and submonoids. Ideally we put these in
  `GroupTheory.Submonoid.Basic`, but currently we cannot because that file is imported by this. -/

namespace Submonoid

variable {s t u : Set M}

@[to_additive (attr := simp)]
/-
**Submonoid.mul_subset** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mul_subset {S : Submonoid M} (hs : s subseteq S) (ht : t subseteq S) : s *
 t subseteq S
参数：hs : s subseteq S；ht : t subseteq S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mul_subset_iff`：mul_subset_iff : s * t subseteq u ↔ forall x in s, f
orall y in t, x * y in u
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
theorem mul_subset {S : Submonoid M} (hs : s ⊆ S) (ht : t ⊆ S) : s * t ⊆ S :=
  mul_subset_iff.2 fun _x hx _y hy ↦ mul_mem (hs hx) (ht hy)

@[to_additive (attr := simp)]
/-
**Submonoid.pow_subset** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：pow_subset {S : Submonoid M} {n : Nat} (hs : s subseteq S) : s ^ n subsete
q S
参数：hs : s subseteq S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
lemma pow_subset {S : Submonoid M} {n : ℕ} (hs : s ⊆ S) : s ^ n ⊆ S := by
  induction n <;> simp [pow_succ, *]

@[to_additive]
/-
**Submonoid.mul_subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mul_subset_closure (hs : s subseteq u) (ht : t subseteq u) : s * t subsete
q Submonoid.closure u
参数：hs : s subseteq u；ht : t subseteq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.mul_subset`：mul_subset {S : Submonoid M} (hs : s subseteq S) (
ht : t subseteq S) : s * t subseteq S
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
-/
theorem mul_subset_closure (hs : s ⊆ u) (ht : t ⊆ u) : s * t ⊆ Submonoid.closure u :=
  mul_subset (Subset.trans hs Submonoid.subset_closure) (Subset.trans ht Submonoid.subset_closure)

@[to_additive]
/-
**Submonoid.coe_mul_self_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_mul_self_eq (s : Submonoid M) : (s : Set M) * s = s
参数：s : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `coe_mul_coe`：coe_mul_coe [SetLike S M] [SubmonoidClass S M] (H : S) : H 
* H = (H : Set M)
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_mul_self_eq (s : Submonoid M) : (s : Set M) * s = s := by
  simp

@[to_additive]
/-
**Submonoid.closure_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_mul_le (S T : Set M) : closure (S * T) <= closure S ⊔ closure T
参数：S T : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem closure_mul_le (S T : Set M) : closure (S * T) ≤ closure S ⊔ closure T :=
  sInf_le fun _x ⟨_s, hs, _t, ht, hx⟩ => hx ▸
    (closure S ⊔ closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
      (SetLike.le_def.mp le_sup_right <| subset_closure ht)
/-
**Submonoid.closure_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {M : Type u_3} [inst : Monoid M] {s : Set M} {n : ℕ}, Submonoid.closure 
(s ^ n) ≤ Submonoid.closure s
参数：s ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[to_additive] lemma closure_pow_le {n : ℕ} : closure (s ^ n) ≤ closure s := by simp

@[to_additive]
/-
**Submonoid.closure_pow_anti** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：closure_pow_anti {m n : Nat} (hmn : m ∣ n) : closure (s ^ n) <= closure (s
 ^ m)
参数：hmn : m ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma closure_pow_anti {m n : ℕ} (hmn : m ∣ n) : closure (s ^ n) ≤ closure (s ^ m) := by
  obtain ⟨k, rfl⟩ := hmn
  simp [pow_mul]

@[to_additive]
/-
**Submonoid.closure_pow** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：closure_pow {n : Nat} (hs : 1 in s) (hn : n != 0) : closure (s ^ n) = clos
ure s
参数：hs : 1 in s；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Submonoid.closure_pow_le`：∀ {M : Type u_3} [inst : Monoid M] {s : Set M}
 {n : ℕ}, Submonoid.closure (s ^ n) ≤ Submonoid.closure s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Submonoid.closure_mono`：closure_mono ⦃s t : Set M⦄ (h : s subseteq t) : 
closure s <= closure t
· 使用引理 `Set.subset_pow`：subset_pow (hs : 1 in s) (hn : n != 0) : s subseteq s ^ 
n
-/
lemma closure_pow {n : ℕ} (hs : 1 ∈ s) (hn : n ≠ 0) : closure (s ^ n) = closure s :=
  closure_pow_le.antisymm <| by grw [← subset_pow hs hn]

@[to_additive]
/-
**Submonoid.sup_eq_closure_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：sup_eq_closure_mul (H K : Submonoid M) : H ⊔ K = closure ((H : Set M) * (K
 : Set M))
参数：H K : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submonoid.closure_mul_le`：closure_mul_le (S T : Set M) : closure (S * T)
 <= closure S ⊔ closure T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.closure_eq`：closure_eq : closure (S : Set M) = S
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem sup_eq_closure_mul (H K : Submonoid M) : H ⊔ K = closure ((H : Set M) * (K : Set M)) :=
  le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, hh, 1, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, H.one_mem, k, hk, one_mul k⟩)
    ((closure_mul_le _ _).trans <| by rw [closure_eq, closure_eq])

@[to_additive]
/-
**Submonoid.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_sup {N : Type*} [CommMonoid N] (H K : Submonoid N) : ↑(H ⊔ K) = (H * K
 : Set N)
参数：H K : Submonoid N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_sup {N : Type*} [CommMonoid N] (H K : Submonoid N) :
    ↑(H ⊔ K) = (H * K : Set N) := by
  ext x
  simp [mem_sup, Set.mem_mul]

@[to_additive]
/-
**Submonoid.pow_smul_mem_closure_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：pow_smul_mem_closure_smul {N : Type*} [CommMonoid N] [MulAction M N] [IsSc
alarTower M N N] (r : M) (s : Set N) {x : N} (hx : x in closure s) : exists n : 
Nat, r ^ n • x in closure (r • s)
参数：r : M；s : Set N；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
-/
theorem pow_smul_mem_closure_smul {N : Type*} [CommMonoid N] [MulAction M N] [IsScalarTower M N N]
    (r : M) (s : Set N) {x : N} (hx : x ∈ closure s) : ∃ n : ℕ, r ^ n • x ∈ closure (r • s) := by
  induction hx using closure_induction with
  | mem x hx => exact ⟨1, subset_closure ⟨_, hx, by rw [pow_one]⟩⟩
  | one => exact ⟨0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨⟨nx, hx⟩, ⟨ny, hy⟩⟩ := And.intro hx hy
    use ny + nx
    rw [pow_add, mul_smul, ← smul_mul_assoc, mul_comm, ← smul_mul_assoc]
    exact mul_mem hy hx

variable [Group G]

/-- The submonoid with every element inverted. -/
@[to_additive (attr := instance_reducible)
  /-- The additive submonoid with every element negated. -/]
/-
**Submonoid.inv** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：{G : Type u_2} → [inst : Group G] → Inv (Submonoid G)
参数：Submonoid G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def inv : Inv (Submonoid G) where
  inv S :=
    { carrier := (S : Set G)⁻¹
      mul_mem' := fun ha hb => by rw [mem_inv, mul_inv_rev]; exact mul_mem hb ha
      one_mem' := mem_inv.2 <| by rw [inv_one]; exact S.one_mem' }

scoped[Pointwise] attribute [instance] Submonoid.inv AddSubmonoid.neg

@[to_additive (attr := simp)]
/-
**Submonoid.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_inv (S : Submonoid G) : ↑S⁻¹ = (S : Set G)⁻¹
参数：S : Submonoid G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv (S : Submonoid G) : ↑S⁻¹ = (S : Set G)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/-
**Submonoid.mem_inv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_inv {g : G} {S : Submonoid G} : g in S⁻¹ ↔ g⁻¹ in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inv {g : G} {S : Submonoid G} : g ∈ S⁻¹ ↔ g⁻¹ ∈ S :=
  Iff.rfl

/-- Inversion is involutive on submonoids. -/
@[to_additive (attr := instance_reducible) /-- Inversion is involutive on additive submonoids. -/]
/-
**Submonoid.involutiveInv** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：involutiveInv : InvolutiveInv (Submonoid G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inversion is involutive on submonoids.
-/
def involutiveInv : InvolutiveInv (Submonoid G) :=
  SetLike.coe_injective.involutiveInv _ fun _ => rfl

scoped[Pointwise] attribute [instance] Submonoid.involutiveInv AddSubmonoid.involutiveNeg

@[to_additive (attr := simp)]
/-
**Submonoid.inv_le_inv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：inv_le_inv (S T : Submonoid G) : S⁻¹ <= T⁻¹ ↔ S <= T
参数：S T : Submonoid G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.inv_subset_inv`：inv_subset_inv : s⁻¹ subseteq t⁻¹ ↔ s subseteq t
-/
theorem inv_le_inv (S T : Submonoid G) : S⁻¹ ≤ T⁻¹ ↔ S ≤ T :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset_inv

@[to_additive]
/-
**Submonoid.inv_le** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：inv_le (S T : Submonoid G) : S⁻¹ <= T ↔ S <= T⁻¹
参数：S T : Submonoid G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.inv_subset`：inv_subset : s⁻¹ subseteq t ↔ s subseteq t⁻¹
-/
theorem inv_le (S T : Submonoid G) : S⁻¹ ≤ T ↔ S ≤ T⁻¹ :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset

/-- Pointwise inversion of submonoids as an order isomorphism. -/
@[to_additive (attr := simps!)
/-- Pointwise negation of additive submonoids as an order isomorphism -/]
/-
**Submonoid.invOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：invOrderIso : Submonoid G ≃o Submonoid G where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.inv_le_inv`：inv_le_inv (S T : Submonoid G) : S⁻¹ <= T⁻¹ ↔ S <=
 T
-/
def invOrderIso : Submonoid G ≃o Submonoid G where
  toEquiv := Equiv.inv _
  map_rel_iff' := inv_le_inv _ _

@[to_additive]
/-
**Submonoid.closure_inv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_inv (s : Set G) : closure s⁻¹ = (closure s)⁻¹
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Submonoid.coe_inv`：coe_inv (S : Submonoid G) : ↑S⁻¹ = (S : Set G)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inv_subset`：inv_subset : s⁻¹ subseteq t ↔ s subseteq t⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Submonoid.inv_le`：inv_le (S T : Submonoid G) : S⁻¹ <= T ↔ S <= T⁻¹
-/
theorem closure_inv (s : Set G) : closure s⁻¹ = (closure s)⁻¹ := by
  apply le_antisymm
  · rw [closure_le, coe_inv, ← Set.inv_subset, inv_inv]
    exact subset_closure
  · rw [inv_le, closure_le, coe_inv, ← Set.inv_subset]
    exact subset_closure

@[to_additive]
/-
**Submonoid.mem_closure_inv** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：mem_closure_inv (s : Set G) (x : G) : x in closure s⁻¹ ↔ x⁻¹ in closure s
参数：s : Set G；x : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.closure_inv`：closure_inv (s : Set G) : closure s⁻¹ = (closure 
s)⁻¹
· 使用定理 `Submonoid.mem_inv`：mem_inv {g : G} {S : Submonoid G} : g in S⁻¹ ↔ g⁻¹ in
 S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_closure_inv (s : Set G) (x : G) : x ∈ closure s⁻¹ ↔ x⁻¹ ∈ closure s := by
  rw [closure_inv, mem_inv]

@[to_additive (attr := simp)]
/-
**Submonoid.inv_inf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：inv_inf (S T : Submonoid G) : (S ⊓ T)⁻¹ = S⁻¹ ⊓ T⁻¹
参数：S T : Submonoid G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.inter_inv`：inter_inv : (s inter t)⁻¹ = s⁻¹ inter t⁻¹
-/
theorem inv_inf (S T : Submonoid G) : (S ⊓ T)⁻¹ = S⁻¹ ⊓ T⁻¹ :=
  SetLike.coe_injective Set.inter_inv

@[to_additive (attr := simp)]
/-
**Submonoid.inv_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：inv_sup (S T : Submonoid G) : (S ⊔ T)⁻¹ = S⁻¹ ⊔ T⁻¹
参数：S T : Submonoid G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem inv_sup (S T : Submonoid G) : (S ⊔ T)⁻¹ = S⁻¹ ⊔ T⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_sup S T

@[to_additive (attr := simp)]
/-
**Submonoid.inv_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：inv_bot : (⊥ : Submonoid G)⁻¹ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inv_singleton`：inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹}
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
theorem inv_bot : (⊥ : Submonoid G)⁻¹ = ⊥ :=
  SetLike.coe_injective <| (Set.inv_singleton 1).trans <| congr_arg _ inv_one

@[to_additive (attr := simp)]
/-
**Submonoid.inv_top** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：inv_top : (⊤ : Submonoid G)⁻¹ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.inv_univ`：inv_univ : (univ : Set α)⁻¹ = univ
-/
theorem inv_top : (⊤ : Submonoid G)⁻¹ = ⊤ :=
  SetLike.coe_injective <| Set.inv_univ

@[to_additive (attr := simp)]
/-
**Submonoid.inv_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：inv_iInf {ι : Sort*} (S : ι -> Submonoid G) : (⨅ i, S i)⁻¹ = ⨅ i, (S i)⁻¹
参数：S : ι -> Submonoid G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
-/
theorem inv_iInf {ι : Sort*} (S : ι → Submonoid G) : (⨅ i, S i)⁻¹ = ⨅ i, (S i)⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_iInf _

@[to_additive (attr := simp)]
/-
**Submonoid.inv_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：inv_iSup {ι : Sort*} (S : ι -> Submonoid G) : (⨆ i, S i)⁻¹ = ⨆ i, (S i)⁻¹
参数：S : ι -> Submonoid G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
theorem inv_iSup {ι : Sort*} (S : ι → Submonoid G) : (⨆ i, S i)⁻¹ = ⨆ i, (S i)⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_iSup _

end Submonoid

namespace Submonoid

section Monoid

variable [Monoid α] [MulDistribMulAction α M]

-- todo: add `to_additive`?
/-- The action on a submonoid corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/-
**Submonoid.pointwiseMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：{α : Type u_1} →   {M : Type u_3} → [inst : Monoid M] → [inst_1 : Monoid α
] → [MulDistribMulAction α M] → MulAction α (Submonoid M)
参数：Submonoid M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on a submonoid corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.
-/
protected def pointwiseMulAction : MulAction α (Submonoid M) where
  smul a S := S.map (MulDistribMulAction.toMonoidEnd _ M a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using! S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : Monoid.End M => S.map f) (map_mul _ _ _)).trans
      (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Submonoid.pointwiseMulAction

@[simp, norm_cast]
/-
**Submonoid.coe_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_pointwise_smul (a : α) (S : Submonoid M) : ↑(a • S) = a • (S : Set M)
参数：a : α；S : Submonoid M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pointwise_smul (a : α) (S : Submonoid M) : ↑(a • S) = a • (S : Set M) :=
  rfl
/-
**Submonoid.smul_mem_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：smul_mem_pointwise_smul (m : M) (a : α) (S : Submonoid M) : m in S -> a • 
m in a • S
参数：m : M；a : α；S : Submonoid M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submonoid M) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CovariantClass α (Submonoid M) HSMul.hSMul LE.le :=
  ⟨fun _ _ => image_mono⟩
/-
**Submonoid.mem_smul_pointwise_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_smul_pointwise_iff_exists (m : M) (a : α) (S : Submonoid M) : m in a •
 S ↔ exists s : M, s in S ∧ a • s = m
参数：m : M；a : α；S : Submonoid M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
-/
theorem mem_smul_pointwise_iff_exists (m : M) (a : α) (S : Submonoid M) :
    m ∈ a • S ↔ ∃ s : M, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set M) ↔ _)

@[simp]
/-
**Submonoid.smul_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：smul_bot (a : α) : a • (⊥ : Submonoid M) = ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.map_bot`：map_bot (f : F) : (⊥ : Submonoid M).map f = ⊥
-/
theorem smul_bot (a : α) : a • (⊥ : Submonoid M) = ⊥ :=
  map_bot _
/-
**Submonoid.smul_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：smul_sup (a : α) (S T : Submonoid M) : a • (S ⊔ T) = a • S ⊔ a • T
参数：a : α；S T : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.map_sup`：map_sup (S T : Submonoid M) (f : F) : (S ⊔ T).map f =
 S.map f ⊔ T.map f
-/
theorem smul_sup (a : α) (S T : Submonoid M) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _
/-
**Submonoid.smul_closure** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：smul_closure (a : α) (s : Set M) : a • closure s = closure (a • s)
参数：a : α；s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mclosure`：map_mclosure (f : F) (s : Set M) : (closure s).m
ap f = closure (f '' s)
-/
theorem smul_closure (a : α) (s : Set M) : a • closure s = closure (a • s) :=
  MonoidHom.map_mclosure _ _
/-
**Submonoid.pointwise_isCentralScalar** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：pointwise_isCentralScalar [MulDistribMulAction αᵐᵒᵖ M] [IsCentralScalar α 
M] : IsCentralScalar α (Submonoid M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
lemma pointwise_isCentralScalar [MulDistribMulAction αᵐᵒᵖ M] [IsCentralScalar α M] :
    IsCentralScalar α (Submonoid M) :=
  ⟨fun _ S => (congr_arg fun f : Monoid.End M => S.map f) <| MonoidHom.ext <| op_smul_eq_smul _⟩

scoped[Pointwise] attribute [instance] Submonoid.pointwise_isCentralScalar

end Monoid

section Group

variable [Group α] [MulDistribMulAction α M]

@[simp]
/-
**Submonoid.smul_mem_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：smul_mem_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : a • x in a
 • S ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
theorem smul_mem_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff
/-
**Submonoid.mem_pointwise_smul_iff_inv_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submo
noid`。
形式化陈述：mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Submonoid M} {x : M} : x 
in a • S ↔ a⁻¹ • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
-/
theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Submonoid M} {x : M} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem
/-
**Submonoid.mem_inv_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_inv_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : x in a⁻¹ • 
S ↔ a • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
-/
theorem mem_inv_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
/-
**Submonoid.pointwise_smul_le_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subm
onoid`。
形式化陈述：pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Submonoid M} : a • S <
= a • T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_smul_set_iff`：smul_set_subset_smul_set_iff : a • A s
ubseteq a • B ↔ A subseteq B
-/
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Submonoid M} : a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff
/-
**Submonoid.pointwise_smul_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：pointwise_smul_subset_iff {a : α} {S T : Submonoid M} : a • S <= T ↔ S <= 
a⁻¹ • T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_iff_subset_inv_smul_set`：smul_set_subset_iff_subset_
inv_smul_set : a • A subseteq B ↔ A subseteq a⁻¹ • B
-/
theorem pointwise_smul_subset_iff {a : α} {S T : Submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  smul_set_subset_iff_subset_inv_smul_set
/-
**Submonoid.subset_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：subset_pointwise_smul_iff {a : α} {S T : Submonoid M} : S <= a • T ↔ a⁻¹ •
 S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
-/
theorem subset_pointwise_smul_iff {a : α} {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_smul_set_iff

end Group
end Submonoid

namespace Set.IsPWO

variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] {s : Set α}

@[to_additive]
/-
**Set.IsPWO.submonoid_closure** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsPWO`。
形式化陈述：submonoid_closure (hpos : forall x : α, x in s -> 1 <= x) (h : s.IsPWO) : 
IsPWO (Submonoid.closure s : Set α)
参数：hpos : forall x : α, x in s -> 1 <= x；h : s.IsPWO。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.closure_eq_image_prod`：closure_eq_image_prod (s : Set M) : (cl
osure s : Set M) = List.prod '' { l : List M | forall x in l, x in s }
· 使用定理 `Set.PartiallyWellOrderedOn.image_of_monotone_on`：∀ {α : Type u_2} {β : T
ype u_3} {r : α → α → Prop} {r' : β → β → Prop} {f : α → β} {s : Set α},   s.Par
tiallyWellOrderedOn r → (∀ a₁ ∈ s, ∀ …
· 使用定理 `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`：partia
llyWellOrderedOn_sublistForall₂ (r : α -> α -> Prop) [IsPreorder α r] {s : Set α
} (h : s.PartiallyWellOrderedOn r) : { l : List α | fo…
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
· 使用定理 `List.SublistForall₂.prod_le_prod'`：∀ {M : Type u_3} [inst : Monoid M] [i
nst_1 : Preorder M] [MulRightMono M] [MulLeftMono M] {l₁ l₂ : List M},   List.Su
blistForall₂ (fun x1 x2…
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
-/
theorem submonoid_closure (hpos : ∀ x : α, x ∈ s → 1 ≤ x) (h : s.IsPWO) :
    IsPWO (Submonoid.closure s : Set α) := by
  rw [Submonoid.closure_eq_image_prod]
  refine (h.partiallyWellOrderedOn_sublistForall₂ (· ≤ ·)).image_of_monotone_on ?_
  exact fun l1 _ l2 hl2 h12 => h12.prod_le_prod' fun x hx => hpos x <| hl2 x hx

end Set.IsPWO

