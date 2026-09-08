/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Notation.Support

/-!
# Miscellaneous lemmas on big operators

The lemmas in this file have been moved out of
`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` to reduce its imports.
-/

public section

variable {ι κ M N β : Type*}

@[to_additive]
/-
**MonoidHom.coe_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.coe_finsetProd [MulOneClass M] [CommMonoid N] (f : ι -> M ->* N)
 (s : Finset ι) : ⇑(∏ x in s, f x) = ∏ x in s, ⇑(f x)
参数：f : ι -> M ->* N；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem MonoidHom.coe_finsetProd [MulOneClass M] [CommMonoid N] (f : ι → M →* N) (s : Finset ι) :
    ⇑(∏ x ∈ s, f x) = ∏ x ∈ s, ⇑(f x) :=
  map_prod (MonoidHom.coeFn M N) _ _

@[deprecated (since := "2026-04-08")]
alias AddMonoidHom.coe_finset_sum := AddMonoidHom.coe_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias MonoidHom.coe_finset_prod := MonoidHom.coe_finsetProd

/-- See also `Finset.prod_apply`, with the same conclusion but with the weaker hypothesis
`f : α → M → N` -/
@[to_additive (attr := simp)
  /-- See also `Finset.sum_apply`, with the same conclusion but with the weaker hypothesis
  `f : α → M → N` -/]
/-
**MonoidHom.finsetProd_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.finsetProd_apply [MulOneClass M] [CommMonoid N] (f : ι -> M ->* 
N) (s : Finset ι) (b : M) : (∏ x in s, f x) b = ∏ x in s, f x b
参数：f : ι -> M ->* N；s : Finset ι；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem MonoidHom.finsetProd_apply [MulOneClass M] [CommMonoid N] (f : ι → M →* N) (s : Finset ι)
    (b : M) : (∏ x ∈ s, f x) b = ∏ x ∈ s, f x b :=
  map_prod (MonoidHom.eval b) _ _

@[deprecated (since := "2026-04-08")]
alias AddMonoidHom.finset_sum_apply := AddMonoidHom.finsetSum_apply

@[to_additive existing, deprecated (since := "2026-04-08")]
alias MonoidHom.finset_prod_apply := MonoidHom.finsetProd_apply

namespace Finset

variable [CommMonoid M]

open Function in
@[to_additive]
/-
**Finset.mulSupport_prod** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulSupport_prod (s : Finset ι) (f : ι -> κ -> M) : mulSupport (fun x => ∏ 
i in s, f i x) subseteq ⋃ i in s, mulSupport (f i)
参数：s : Finset ι；f : ι -> κ -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
-/
lemma mulSupport_prod (s : Finset ι) (f : ι → κ → M) :
    mulSupport (fun x ↦ ∏ i ∈ s, f i x) ⊆ ⋃ i ∈ s, mulSupport (f i) := by
  simp only [mulSupport_subset_iff', Set.mem_iUnion, not_exists, notMem_mulSupport]
  exact fun x ↦ prod_eq_one

@[to_additive]
/-
**Finset.isSquare_prod** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：isSquare_prod {s : Finset ι} (f : ι -> M) (h : forall c in s, IsSquare (f 
c)) : IsSquare (∏ i in s, f i)
参数：f : ι -> M；h : forall c in s, IsSquare (f c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isSquare_iff_exists_sq`：isSquare_iff_exists_sq (a : α) : IsSquare a ↔ ex
ists r, a = r ^ 2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.prod_coe_sort`：prod_coe_sort : ∏ i : s, f i = ∏ i in s, f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma isSquare_prod {s : Finset ι} (f : ι → M) (h : ∀ c ∈ s, IsSquare (f c)) :
    IsSquare (∏ i ∈ s, f i) := by
  rw [isSquare_iff_exists_sq]
  use (∏ (x : s), ((isSquare_iff_exists_sq _).mp (h _ x.2)).choose)
  rw [@sq, ← Finset.prod_mul_distrib, ← Finset.prod_coe_sort]
  congr
  ext i
  rw [← @sq]
  exact ((isSquare_iff_exists_sq _).mp (h _ i.2)).choose_spec

end Finset

