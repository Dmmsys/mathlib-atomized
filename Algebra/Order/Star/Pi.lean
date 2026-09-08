/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Group.Submonoid.Finite
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.Pi

/-!
# Pi-types of star-ordered rings
-/

public section

variable {ι : Type*} [Finite ι]
  {A : ι → Type*} [Π i, PartialOrder (A i)] [Π i, NonUnitalSemiring (A i)]
  [Π i, StarRing (A i)] [∀ i, StarOrderedRing (A i)]

open AddSubmonoid in
/-
**Pi.instStarOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instStarOrderedRing : StarOrderedRing (Π i, A i) where le_iff xa xy
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubmonoid.closure_pi`：∀ {η : Type u_1} {f : η → Type u_2} [inst : (i 
: η) → AddZeroClass (f i)] [Finite η] {s : (i : η) → Set (f i)},   (∀ (i : η), 0
 ∈ s i) →    …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
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
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance Pi.instStarOrderedRing : StarOrderedRing (Π i, A i) where
  le_iff xa xy := by
    have : closure (Set.range fun s : Π i, A i ↦ star s * s) =
        pi Set.univ fun i => (closure <| Set.range fun s : A i ↦ star s * s) := by
      rw [← closure_pi fun _ => Set.mem_range.mpr ⟨0, by simp⟩]
      congr
      ext x
      simp only [Set.mem_range, funext_iff, mul_apply, star_apply, Set.mem_pi,
        Set.mem_univ, forall_const]
      exact ⟨fun ⟨y, hy⟩ i => ⟨y i, hy i⟩, fun h => ⟨fun i => h i |>.choose,
        fun i => h i |>.choose_spec⟩⟩
    simp only [this, Pi.le_def, StarOrderedRing.le_iff, mem_pi, Set.mem_univ, forall_const]
    refine ⟨fun h => ?_, ?_⟩
    · simp only [funext_iff, add_apply]
      exact ⟨fun i => h i |>.choose, fun i => h i |>.choose_spec.1, fun i => h i |>.choose_spec.2⟩
    · simp only [forall_exists_index, and_imp]
      intro x h rfl i
      exact ⟨x i, by simp [h]⟩
