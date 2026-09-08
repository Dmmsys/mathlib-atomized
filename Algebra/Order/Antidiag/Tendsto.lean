/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Order.Filter.Cofinite

/-!
# Antidiagonal tendsto

`tendsto_sup'_antidiagonal_cofinite`: If a function `f : M × M → R` on a Finset `M`, that has the
  antidiagonal propertry,  tends to to a filter `F` under the cofinite filter then so does the
  function assigning to `x : M` its supremum of its antidiagonal.
-/

@[expose] public section

namespace Finset.HasAntidiagonal

open Filter

variable {M R : Type*} [AddMonoid M] [HasAntidiagonal M] {f : M × M → R} [LinearOrder R]
  {F : Filter R}

/-
**Finset.HasAntidiagonal.tendsto_sup'_antidiagonal_cofinite** 是 Mathlib 中的一个定理，位
于命名空间 `Finset.HasAntidiagonal`。
形式化陈述：∀ {M : Type u_1} {R : Type u_2} [inst : AddMonoid M] [inst_1 : Finset.HasA
ntidiagonal M] {f : M × M → R}   [inst_2 : LinearOrder R] {F : Filter R},   Filt
er.Tendsto f Filter.cofinite F →     Filter.Tendsto (fun a => (Finset.HasAntidia
gonal.antidiagonal a).sup' ⋯ f) Filter.cofinite F
参数：fun a => (Finset.HasAntidiagonal.antidiagonal a).sup' ⋯ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α}, s.Finite 
→ t.Finite → (s + t).Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.HasAntidiagonal.nonempty_antidiagonal`：∀ {M : Type u_2} [inst : A
ddMonoid M] [inst_1 : Finset.HasAntidiagonal M] (a : M),   (Finset.HasAntidiagon
al.antidiagonal a).Nonempty
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.exists_mem_eq_sup'`：exists_mem_eq_sup' (f : ι -> α) : exists i, i
 in s ∧ s.sup' H f = f i
· 使用定理 `Set.add_mem_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α} {a b : α}
, a ∈ s → b ∈ t → a + b ∈ s + t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma tendsto_sup'_antidiagonal_cofinite (hf : Tendsto f cofinite F) : Tendsto
    (fun a ↦ (Finset.antidiagonal a).sup' (nonempty_antidiagonal _) f) cofinite F := by
  intro U hU
  refine ((((hf hU).image Prod.fst)).add ((hf hU).image Prod.snd)).subset ?_
  simp only [Set.subset_def, Set.mem_compl_iff, Set.mem_preimage]
  intro x hx
  obtain ⟨i, hi, e⟩ := Finset.exists_mem_eq_sup' (nonempty_antidiagonal x) f
  obtain rfl : i.1 + i.2 = x := by simpa using hi
  exact Set.add_mem_add (by simpa using ⟨i.2, e ▸ hx⟩) (by simpa using ⟨i.1, e ▸ hx⟩)

end Finset.HasAntidiagonal

