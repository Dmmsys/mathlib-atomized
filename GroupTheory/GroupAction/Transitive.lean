/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Hom

/-! # Complements to pretransitive actions

When `f : X →ₑ[φ] Y` is an equivariant map with respect to a map
of monoids `φ: M → N`,

- `MulAction.IsPretransitive.of_surjective_map` shows that
  the action of `N` on `Y` is pretransitive
  if that of `M` on `X`  is pretransitive.

- `MulAction.isPretransitive_congr` shows that when
  `φ` is surjective, the action of `N` on `Y` is pretransitive
  iff that of `M` on `X`  is pretransitive.

Given `MulAction G X` where `G` is a group,
- `MulAction.isPretransitive_iff_base G a` shows that `IsPretransitive G X`
  iff every element is translated from `a`

- `MulAction.isPretransitive_iff_orbit_eq_univ G a` shows that `MulAction.IsPretransitive G X`
  iff `MulAction.orbit G a` is full.

-/

public section

variable {G X : Type*} [Group G] [MulAction G X]

namespace MulAction

/-- An action of a group is pretransitive iff any element can be moved from a fixed given one. -/
@[to_additive
  /-- An additive action of an additive group is pretransitive
  iff any element can be moved from a fixed given one. -/]
/-
**MulAction.isPretransitive_iff_base** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：isPretransitive_iff_base (a : X) : IsPretransitive G X ↔ forall x : X, exi
sts g : G, g • a = x where mp hG x
参数：a : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
theorem isPretransitive_iff_base (a : X) :
    IsPretransitive G X ↔ ∀ x : X, ∃ g : G, g • a = x where
  mp hG x := exists_smul_eq _ a x
  mpr hG := .mk fun x y ↦ by
    obtain ⟨g, hx⟩ := hG x
    obtain ⟨h, hy⟩ := hG y
    exact ⟨h * g⁻¹, by rw [← hx, smul_smul, inv_mul_cancel_right, hy]⟩

/-- An action of a group is pretransitive iff the orbit of every given element is full -/
@[to_additive
  /-- An action of a group is pretransitive iff the orbit of every given element is full -/]
/-
**MulAction.isPretransitive_iff_orbit_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `MulActi
on`。
形式化陈述：isPretransitive_iff_orbit_eq_univ (a : X) : IsPretransitive G X ↔ orbit G 
a = .univ
参数：a : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.isPretransitive_iff_base`：isPretransitive_iff_base (a : X) : I
sPretransitive G X ↔ forall x : X, exists g : G, g • a = x where mp hG x
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPretransitive_iff_orbit_eq_univ (a : X) :
    IsPretransitive G X ↔ orbit G a = .univ := by
  rw [isPretransitive_iff_base a, Set.ext_iff]
  apply forall_congr'
  intro x
  simp_rw [Set.mem_univ, iff_true, mem_orbit_iff]

variable {M N α β : Type*} [Monoid M] [Monoid N] [MulAction M α] [MulAction N β]

@[to_additive]
/-
**MulAction.IsPretransitive.of_surjective_map** 是 Mathlib 中的一个定理，位于命名空间 `MulActi
on.IsPretransitive`。
形式化陈述：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} {β : Type u_6} [inst : Mono
id M] [inst_1 : Monoid N]   [inst_2 : MulAction M α] [inst_3 : MulAction N β] {φ
 : M → N} {f : α →ₑ[φ] β},   Function.Surjective ⇑f → MulAction.IsPretransitive 
M α → MulAction.IsPretransitive N β
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPretransitive.exists_smul_eq`：∀ {M : Type u_5} {α : Type u_6
} {inst : SMul M α} [self : MulAction.IsPretransitive M α] (x y : α), ∃ g, g • x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsPretransitive.of_surjective_map {φ : M → N} {f : α →ₑ[φ] β}
    (hf : Function.Surjective f) (h : IsPretransitive M α) :
    IsPretransitive N β := by
  apply MulAction.IsPretransitive.mk
  intro x y
  obtain ⟨x', rfl⟩ := hf x
  obtain ⟨y', rfl⟩ := hf y
  obtain ⟨g, rfl⟩ := h.exists_smul_eq x' y'
  exact ⟨φ g, by simp only [map_smulₛₗ]⟩

@[to_additive]
/-
**MulAction.isPretransitive_congr** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：isPretransitive_congr {φ : M -> N} {f : α ->ₑ[φ] β} (hφ : Function.Surject
ive φ) (hf : Function.Bijective f) : IsPretransitive M α ↔ IsPretransitive N β
参数：hφ : Function.Surjective φ；hf : Function.Bijective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPretransitive.of_surjective_map`：∀ {M : Type u_3} {N : Type 
u_4} {α : Type u_5} {β : Type u_6} [inst : Monoid M] [inst_1 : Monoid N]   [inst
_2 : MulAction M α] [inst_3 : Mul…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `MulAction.IsPretransitive.exists_smul_eq`：∀ {M : Type u_5} {α : Type u_6
} {inst : SMul M α} [self : MulAction.IsPretransitive M α] (x y : α), ∃ g, g • x
 = y
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isPretransitive_congr {φ : M → N} {f : α →ₑ[φ] β}
    (hφ : Function.Surjective φ) (hf : Function.Bijective f) :
    IsPretransitive M α ↔ IsPretransitive N β := by
  constructor
  · apply IsPretransitive.of_surjective_map hf.surjective
  · intro hN
    apply IsPretransitive.mk
    intro x y
    obtain ⟨k, hk⟩ := hN.exists_smul_eq (f x) (f y)
    obtain ⟨g, rfl⟩ := hφ k
    use g
    apply hf.injective
    simp only [hk, map_smulₛₗ]

end MulAction

