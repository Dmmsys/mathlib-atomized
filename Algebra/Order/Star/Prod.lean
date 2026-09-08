/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.Prod
public import Mathlib.Algebra.Ring.Prod

/-!
# Products of star-ordered rings
-/

public section

variable {α β : Type*}

open AddSubmonoid in
/-
**Prod.instStarOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instStarOrderedRing [NonUnitalSemiring α] [NonUnitalSemiring β] [Part
ialOrder α] [PartialOrder β] [StarRing α] [StarRing β] [StarOrderedRing α] [Star
OrderedRing β] : StarOrderedRing (α × β) where le_iff
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.forall`：∀ {α : Type u_1} {β : Type u_2} {p : α × β → Prop}, (∀ (x :
 α × β), p x) ↔ ∀ (a : α) (b : β), p (a, b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubmonoid.closure_prod`：∀ {N : Type u_2} [inst : AddZeroClass N] {M :
 Type u_5} [inst_1 : AddZeroClass M] {s : Set M} {t : Set N},   0 ∈ s → 0 ∈ t → 
AddSubmonoid.cl…
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.prod_range_range_eq`：prod_range_range_eq {m₁ : α -> γ} {m₂ : β -> δ}
 : range m₁ ×ˢ range m₂ = range fun p : α × β => (m₁ p.1, m₂ p.2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
instance Prod.instStarOrderedRing
    [NonUnitalSemiring α] [NonUnitalSemiring β] [PartialOrder α] [PartialOrder β]
    [StarRing α] [StarRing β] [StarOrderedRing α] [StarOrderedRing β] :
    StarOrderedRing (α × β) where
  le_iff := Prod.forall.2 fun xa xy => Prod.forall.2 fun ya yb => by
    have :
        closure (Set.range fun s : α × β ↦ star s * s) =
          (closure <| Set.range fun s : α ↦ star s * s).prod
          (closure <| Set.range fun s : β ↦ star s * s) := by
      rw [← closure_prod (Set.mem_range.2 ⟨0, by simp⟩) (Set.mem_range.2 ⟨0, by simp⟩),
        Set.prod_range_range_eq]
      simp_rw [Prod.mul_def, Prod.star_def]
    simp only [mk_le_mk, Prod.exists, mk_add_mk, mk.injEq, StarOrderedRing.le_iff, this,
      AddSubmonoid.mem_prod, exists_and_exists_comm, and_and_and_comm]
