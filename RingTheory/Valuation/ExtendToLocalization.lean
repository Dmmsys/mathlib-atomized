/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Valuation.Basic

/-!

# Extending valuations to a localization

We show that, given a valuation `v` taking values in a linearly ordered commutative *group*
with zero `Γ`, and a submonoid `S` of `v.supp.primeCompl`, the valuation `v` can be naturally
extended to the localization `S⁻¹A`.

-/

@[expose] public section


variable {A : Type*} [CommRing A] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation A Γ) {S : Submonoid A} (hS : S ≤ v.supp.primeCompl) (B : Type*) [CommRing B]
  [Algebra A B] [IsLocalization S B]

/-- We can extend a valuation `v` on a ring to a localization at a submonoid of
the complement of `v.supp`. -/
/-
**Valuation.extendToLocalization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Valuation.extendToLocalization : Valuation B Γ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can extend a valuation `v` on a ring to a localization at a submonoid of
the complement of `v.supp`.
-/
noncomputable def Valuation.extendToLocalization : Valuation B Γ :=
  let f := IsLocalization.toLocalizationMap S B
  let h : ∀ s : S, IsUnit (v.1.toMonoidHom s) := fun s => isUnit_iff_ne_zero.2 (hS s.2)
  { f.lift h with
    map_zero' := by convert! f.lift_eq (P := Γ) _ 0 <;> simp [f]
    map_add_le_max' := fun x y => by
      obtain ⟨a, b, s, rfl, rfl⟩ : ∃ (a b : A) (s : S), f.mk' a s = x ∧ f.mk' b s = y := by
        obtain ⟨a, s, rfl⟩ := f.mk'_surjective x
        obtain ⟨b, t, rfl⟩ := f.mk'_surjective y
        use a * t, b * s, s * t
        constructor <;>
          · rw [f.mk'_eq_iff_eq, Submonoid.coe_mul]
            ring_nf
      convert_to! f.lift h (f.mk' (a + b) s) ≤ max (f.lift h _) (f.lift h _)
      · refine congr_arg (f.lift h) (IsLocalization.eq_mk'_iff_mul_eq.2 ?_)
        rw [add_mul, map_add]
        rw [← IsLocalization.toLocalizationMap_apply S B, f.mk'_spec, f.mk'_spec,
          IsLocalization.toLocalizationMap_apply,
          IsLocalization.toLocalizationMap_apply]
      iterate 3 rw [f.lift_mk']
      dsimp
      grw [max_mul_mul_right, v.map_add a b] }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Valuation.extendToLocalization_mk'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Valuation.extendToLocalization_mk' (x : A) (y : S) : (v.extendToLocalizati
on hS B) (IsLocalization.mk' _ x y) = v x * (v y)⁻¹
参数：x : A；y : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.instIsPrimeSuppOfNontrivialOfNoZeroDivisors`：∀ {R : Type u_3} 
{Γ₀ : Type u_4} [inst : CommRing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀
] (v : Valuation R Γ₀)   [Nontrivial Γ₀] [N…
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.lift_mk'`：lift_mk' (x y) : f.lift hg (f.mk' x 
y) = g x * (IsUnit.liftRight (g.domRestrict S) hg y)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Valuation.extendToLocalization_mk' (x : A) (y : S) :
    (v.extendToLocalization hS B) (IsLocalization.mk' _ x y) =
      v x * (v y)⁻¹ :=
  (Submonoid.LocalizationMap.lift_mk' _ _ _ _).trans (by simp [IsUnit.coe_liftRight])

@[simp]
/-
**Valuation.extendToLocalization_apply_map_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Valuation.extendToLocalization_apply_map_apply (a : A) : v.extendToLocaliz
ation hS B (algebraMap A B a) = v a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.instIsPrimeSuppOfNontrivialOfNoZeroDivisors`：∀ {R : Type u_3} 
{Γ₀ : Type u_4} [inst : CommRing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀
] (v : Valuation R Γ₀)   [Nontrivial Γ₀] [N…
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `Submonoid.LocalizationMap.lift_eq`：lift_eq (x : M) : f.lift hg (f x) = g
 x
-/
theorem Valuation.extendToLocalization_apply_map_apply (a : A) :
    v.extendToLocalization hS B (algebraMap A B a) = v a :=
  Submonoid.LocalizationMap.lift_eq _ _ a
