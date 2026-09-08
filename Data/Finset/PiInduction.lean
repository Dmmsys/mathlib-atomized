/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Fintype.Basic

/-!
# Induction principles for `∀ i, Finset (α i)`

In this file we prove a few induction principles for functions `Π i : ι, Finset (α i)` defined on a
finite type.

* `Finset.induction_on_pi` is a generic lemma that requires only `[Finite ι]`, `[DecidableEq ι]`,
  and `[∀ i, DecidableEq (α i)]`; this version can be seen as a direct generalization of
  `Finset.induction_on`.

* `Finset.induction_on_pi_max` and `Finset.induction_on_pi_min`: generalizations of
  `Finset.induction_on_max`; these versions require `∀ i, LinearOrder (α i)` but assume
  `∀ y ∈ g i, y < x` and `∀ y ∈ g i, x < y` respectively in the induction step.

## Tags
finite set, finite type, induction, function
-/

public section


open Function

variable {ι : Type*} {α : ι → Type*} [Finite ι] [DecidableEq ι] [∀ i, DecidableEq (α i)]

namespace Finset

/-- General theorem for `Finset.induction_on_pi`-style induction principles. -/
/-
**Finset.induction_on_pi_of_choice** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：induction_on_pi_of_choice (r : forall i, α i -> Finset (α i) -> Prop) (H_e
x : forall (i) (s : Finset (α i)), s.Nonempty -> exists x in s, r i x (s.erase x
)) {p : (forall i, Finset (α i)) -> Prop} (f : forall i, Finset (α i)) (h0 : p f
un _ => ∅) (step : forall (g : forall i, Finset (α i)) (i : ι) (x : α i), r i x 
(g i) -> p g -> p (update g i (insert x (g i)))) : p f
参数：r : forall i, α i -> Finset (α i) -> Prop；H_ex : forall (i) (s : Finset (α i)
), s.Nonempty -> exists x in s, r i x (s.erase x)；forall i, Finset (α i)；f : for
all i, Finset (α i)；h0 : p fun _ => ∅；step : forall (g : forall i, Finset (α i))
 (i : ι) (x : α i), r i x (g i) -> p g -> p (update g i (insert x (g i)))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.sigma_nonempty`：sigma_nonempty : (s.sigma t).Nonempty ↔ exists i 
in s, (t i).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Function.update_idem`：update_idem {α} [DecidableEq α] {β : α -> Sort*} {
a : α} (v w : β a) (f : forall a, β a) : update (update f a v) a w = update f a 
w
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `Finset.ssubset_iff_of_subset`：ssubset_iff_of_subset {s₁ s₂ : Finset α} (
h : s₁ subseteq s₂) : s₁ ⊂ s₂ ↔ exists x in s₂, x ∉ s₁
· 使用定理 `Finset.sigma_mono`：sigma_mono (hs : s₁ subseteq s₂) (ht : forall i, t₁ i
 subseteq t₂ i) : s₁.sigma t₁ subseteq s₂.sigma t₂
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_update_iff`：le_update_iff : x <= Function.update y i a ↔ x i <= a ∧ f
orall (j) (_ : j != i), x j <= y j
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Finset.mem_sigma`：mem_sigma {a : Σ i, α i} : a in s.sigma t ↔ a.1 in s ∧
 a.2 in t a.1
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
General theorem for `Finset.induction_on_pi`-style induction principles.
-/
theorem induction_on_pi_of_choice (r : ∀ i, α i → Finset (α i) → Prop)
    (H_ex : ∀ (i) (s : Finset (α i)), s.Nonempty → ∃ x ∈ s, r i x (s.erase x))
    {p : (∀ i, Finset (α i)) → Prop} (f : ∀ i, Finset (α i)) (h0 : p fun _ ↦ ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i),
        r i x (g i) → p g → p (update g i (insert x (g i)))) :
    p f := by
  cases nonempty_fintype ι
  induction hs : univ.sigma f using Finset.strongInductionOn generalizing f with | _ s ihs
  subst s
  rcases eq_empty_or_nonempty (univ.sigma f) with he | hne
  · convert! h0 using 1
    simpa [funext_iff] using he
  · rcases sigma_nonempty.1 hne with ⟨i, -, hi⟩
    rcases H_ex i (f i) hi with ⟨x, x_mem, hr⟩
    set g := update f i ((f i).erase x) with hg
    clear_value g
    have hx' : x ∉ g i := by
      rw [hg, update_self]
      apply notMem_erase
    rw [show f = update g i (insert x (g i)) by
      rw [hg, update_idem, update_self, insert_erase x_mem, update_eq_self]] at hr ihs ⊢
    clear hg
    rw [update_self, erase_insert hx'] at hr
    refine step _ _ _ hr (ihs (univ.sigma g) ?_ _ rfl)
    rw [ssubset_iff_of_subset (sigma_mono (Subset.refl _) _)]
    exacts [⟨⟨i, x⟩, mem_sigma.2 ⟨mem_univ _, by simp⟩, by simp [hx']⟩,
      (@le_update_iff _ _ _ _ g g i _).2 ⟨subset_insert _ _, fun _ _ ↦ le_rfl⟩]

/-- Given a predicate on functions `∀ i, Finset (α i)` defined on a finite type, it is true on all
maps provided that it is true on `fun _ ↦ ∅` and for any function `g : ∀ i, Finset (α i)`, an index
`i : ι`, and `x ∉ g i`, `p g` implies `p (update g i (insert x (g i)))`.

See also `Finset.induction_on_pi_max` and `Finset.induction_on_pi_min` for specialized versions
that require `∀ i, LinearOrder (α i)`. -/
/-
**Finset.induction_on_pi** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：induction_on_pi {p : (forall i, Finset (α i)) -> Prop} (f : forall i, Fins
et (α i)) (h0 : p fun _ => ∅) (step : forall (g : forall i, Finset (α i)) (i : ι
), forall x ∉ g i, p g -> p (update g i (insert x (g i)))) : p f
参数：forall i, Finset (α i)；f : forall i, Finset (α i)；h0 : p fun _ => ∅；step : fo
rall (g : forall i, Finset (α i)) (i : ι), forall x ∉ g i, p g -> p (update g i 
(insert x (g i)))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on_pi_of_choice`：induction_on_pi_of_choice (r : forall 
i, α i -> Finset (α i) -> Prop) (H_ex : forall (i) (s : Finset (α i)), s.Nonempt
y -> exists x in s, r …
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a

--- 原说明 ---
Given a predicate on functions `∀ i, Finset (α i)` defined on a finite type, it 
is true on all
maps provided that it is true on `fun _ ↦ ∅` and for any function `g : ∀ i, Fins
et (α i)`, an index
`i : ι`, and `x ∉ g i`, `p g` implies `p (update g i (insert x (g i)))`.

See also `Finset.induction_on_pi_max` and `Finset.induction_on_pi_min` for speci
alized versions
that require `∀ i, LinearOrder (α i)`.
-/
theorem induction_on_pi {p : (∀ i, Finset (α i)) → Prop} (f : ∀ i, Finset (α i)) (h0 : p fun _ ↦ ∅)
    (step : ∀ (g : ∀ i, Finset (α i)) (i : ι), ∀ x ∉ g i, p g → p (update g i (insert x (g i)))) :
    p f :=
  induction_on_pi_of_choice (fun _ x s ↦ x ∉ s) (fun _ s ⟨x, hx⟩ ↦ ⟨x, hx, notMem_erase x s⟩) f
    h0 step

/-- Given a predicate on functions `∀ i, Finset (α i)` defined on a finite type, it is true on all
maps provided that it is true on `fun _ ↦ ∅` and for any function `g : ∀ i, Finset (α i)`, an index
`i : ι`, and an element `x : α i` that is strictly greater than all elements of `g i`, `p g` implies
`p (update g i (insert x (g i)))`.

This lemma requires `LinearOrder` instances on all `α i`. See also `Finset.induction_on_pi` for a
version that needs `x ∉ g i` and does not need `∀ i, LinearOrder (α i)`. -/
/-
**Finset.induction_on_pi_max** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：induction_on_pi_max [forall i, LinearOrder (α i)] {p : (forall i, Finset (
α i)) -> Prop} (f : forall i, Finset (α i)) (h0 : p fun _ => ∅) (step : forall (
g : forall i, Finset (α i)) (i : ι) (x : α i), (forall y in g i, y < x) -> p g -
> p (update g i (insert x (g i)))) : p f
参数：α i；forall i, Finset (α i)；f : forall i, Finset (α i)；h0 : p fun _ => ∅；step 
: forall (g : forall i, Finset (α i)) (i : ι) (x : α i), (forall y in g i, y < x
) -> p g -> p (update g i (insert x (g i)))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on_pi_of_choice`：induction_on_pi_of_choice (r : forall 
i, α i -> Finset (α i) -> Prop) (H_ex : forall (i) (s : Finset (α i)), s.Nonempt
y -> exists x in s, r …
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `Finset.lt_max'_of_mem_erase_max'`：∀ {α : Type u_2} [inst : LinearOrder α
] (s : Finset α) (H : s.Nonempty) [inst_1 : DecidableEq α] {a : α},   a ∈ s.eras
e (s.max' H) → a < s.m…

--- 原说明 ---
Given a predicate on functions `∀ i, Finset (α i)` defined on a finite type, it 
is true on all
maps provided that it is true on `fun _ ↦ ∅` and for any function `g : ∀ i, Fins
et (α i)`, an index
`i : ι`, and an element `x : α i` that is strictly greater than all elements of 
`g i`, `p g` implies
`p (update g i (insert x (g i)))`.

This lemma requires `LinearOrder` instances on all `α i`. See also `Finset.induc
tion_on_pi` for a
version that needs `x ∉ g i` and does not need `∀ i, LinearOrder (α i)`.
-/
theorem induction_on_pi_max [∀ i, LinearOrder (α i)] {p : (∀ i, Finset (α i)) → Prop}
    (f : ∀ i, Finset (α i)) (h0 : p fun _ ↦ ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i),
        (∀ y ∈ g i, y < x) → p g → p (update g i (insert x (g i)))) :
    p f :=
  induction_on_pi_of_choice (fun _ x s ↦ ∀ y ∈ s, y < x)
    (fun _ s hs ↦ ⟨s.max' hs, s.max'_mem hs, fun _ ↦ s.lt_max'_of_mem_erase_max' _⟩) f h0 step

/-- Given a predicate on functions `∀ i, Finset (α i)` defined on a finite type, it is true on all
maps provided that it is true on `fun _ ↦ ∅` and for any function `g : ∀ i, Finset (α i)`, an index
`i : ι`, and an element `x : α i` that is strictly less than all elements of `g i`, `p g` implies
`p (update g i (insert x (g i)))`.

This lemma requires `LinearOrder` instances on all `α i`. See also `Finset.induction_on_pi` for a
version that needs `x ∉ g i` and does not need `∀ i, LinearOrder (α i)`. -/
/-
**Finset.induction_on_pi_min** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：induction_on_pi_min [forall i, LinearOrder (α i)] {p : (forall i, Finset (
α i)) -> Prop} (f : forall i, Finset (α i)) (h0 : p fun _ => ∅) (step : forall (
g : forall i, Finset (α i)) (i : ι) (x : α i), (forall y in g i, x < y) -> p g -
> p (update g i (insert x (g i)))) : p f
参数：α i；forall i, Finset (α i)；f : forall i, Finset (α i)；h0 : p fun _ => ∅；step 
: forall (g : forall i, Finset (α i)) (i : ι) (x : α i), (forall y in g i, x < y
) -> p g -> p (update g i (insert x (g i)))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on_pi_max`：induction_on_pi_max [forall i, LinearOrder (
α i)] {p : (forall i, Finset (α i)) -> Prop} (f : forall i, Finset (α i)) (h0 : 
p fun _ => ∅) (s…

--- 原说明 ---
Given a predicate on functions `∀ i, Finset (α i)` defined on a finite type, it 
is true on all
maps provided that it is true on `fun _ ↦ ∅` and for any function `g : ∀ i, Fins
et (α i)`, an index
`i : ι`, and an element `x : α i` that is strictly less than all elements of `g 
i`, `p g` implies
`p (update g i (insert x (g i)))`.

This lemma requires `LinearOrder` instances on all `α i`. See also `Finset.induc
tion_on_pi` for a
version that needs `x ∉ g i` and does not need `∀ i, LinearOrder (α i)`.
-/
theorem induction_on_pi_min [∀ i, LinearOrder (α i)] {p : (∀ i, Finset (α i)) → Prop}
    (f : ∀ i, Finset (α i)) (h0 : p fun _ ↦ ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i),
        (∀ y ∈ g i, x < y) → p g → p (update g i (insert x (g i)))) :
    p f :=
  induction_on_pi_max (α := fun i ↦ (α i)ᵒᵈ) _ h0 step

end Finset

