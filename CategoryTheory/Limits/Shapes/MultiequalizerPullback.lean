/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Multicoequalizers that are pushouts

In this file, we show that a multicoequalizer for
`I : MultispanIndex (.ofLinearOrder ι) C` is also
a pushout when `ι` has exactly two elements.

-/

@[expose] public section

namespace CategoryTheory.Limits.Multicofork.IsColimit

variable {C : Type*} [Category* C] {J : MultispanShape} [Unique J.L]
  {I : MultispanIndex J C} (c : Multicofork I)
  (h : {J.fst default, J.snd default} = Set.univ) (h' : J.fst default ≠ J.snd default)

namespace isPushout

variable (s : PushoutCocone (I.fst default) (I.snd default))

open scoped Classical in
/-- Given a multispan shape `J` which is essentially `.ofLinearOrder ι`
(where `ι` has exactly two elements), this is the multicofork
deduced from a pushout cocone. -/
/-
**CategoryTheory.Limits.Multicofork.IsColimit.isPushout.multicofork** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Limits.Multicofork.IsColimit.isPushout`。
形式化陈述：multicofork : Multicofork I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a multispan shape `J` which is essentially `.ofLinearOrder ι`
(where `ι` has exactly two elements), this is the multicofork
deduced from a pushout cocone.
-/
noncomputable def multicofork : Multicofork I :=
  Multicofork.ofπ _ s.pt
    (fun k ↦
      if hk : k = J.fst default then
        eqToHom (by simp [hk]) ≫ s.inl
      else
        eqToHom (by
          obtain rfl : k = J.snd default := by
            have := h.symm.le (Set.mem_univ k)
            push _ ∈ _ at this
            tauto
          rfl) ≫ s.inr)
    (by
      rw [Unique.forall_iff]
      simpa [h'.symm] using s.condition)

@[simp]
/-
**CategoryTheory.Limits.Multicofork.IsColimit.isPushout.multicofork_** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Limits.Multicofork.IsColimit.isPushout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma multicofork_π_eq_inl : (multicofork h h' s).π (J.fst default) = s.inl := by
  dsimp only [multicofork, ofπ, π]
  rw [dif_pos rfl, eqToHom_refl, Category.id_comp]

@[simp]
/-
**CategoryTheory.Limits.Multicofork.IsColimit.isPushout.multicofork_** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Limits.Multicofork.IsColimit.isPushout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma multicofork_π_eq_inr : (multicofork h h' s).π (J.snd default) = s.inr := by
  dsimp only [multicofork, ofπ, π]
  rw [dif_neg h'.symm, eqToHom_refl, Category.id_comp]

end isPushout

include h h' in
/-- A multicoequalizer for `I : MultispanIndex J C` is also
a pushout when `J` is essentially `.ofLinearOrder ι` where
`ι` contains exactly two elements. -/
/-
**CategoryTheory.Limits.Multicofork.IsColimit.isPushout** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits.Multicofork.IsColimit`。
形式化陈述：isPushout (hc : IsColimit c) : IsPushout (I.fst default) (I.snd default) (
c.π (J.fst default)) (c.π (J.snd default)) where w
参数：hc : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multicofork.condition`：condition (a) : I.fst a ≫ K
.π (J.fst a) = I.snd a ≫ K.π (J.snd a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Limits.Multicofork.IsColimit.isPushout.multicofork_π_eq_i
nl`：multicofork_π_eq_inl : (multicofork h h' s).π (J.fst default) = s.inl
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.Multicofork.IsColimit.isPushout.multicofork_π_eq_i
nr`：multicofork_π_eq_inr : (multicofork h h' s).π (J.snd default) = s.inr
· 使用定理 `CategoryTheory.Limits.Multicofork.IsColimit.hom_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MultispanShape}
   {I : CategoryTheory.Limits.MultispanIn…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
A multicoequalizer for `I : MultispanIndex J C` is also
a pushout when `J` is essentially `.ofLinearOrder ι` where
`ι` contains exactly two elements.
-/
lemma isPushout (hc : IsColimit c) :
    IsPushout (I.fst default) (I.snd default) (c.π (J.fst default)) (c.π (J.snd default)) where
  w := c.condition _
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ hc.desc (isPushout.multicofork h h' s))
    (fun s ↦ by simpa using! hc.fac (isPushout.multicofork h h' s) (.right (J.fst default)))
    (fun s ↦ by simpa using! hc.fac (isPushout.multicofork h h' s) (.right (J.snd default)))
    (fun s m h₁ h₂ ↦ by
      apply Multicofork.IsColimit.hom_ext hc
      intro k
      have := h.symm.le (Set.mem_univ k)
      push _ ∈ _ at this
      obtain rfl | rfl := this
      · simpa [h₁] using! (hc.fac (isPushout.multicofork h h' s) (.right (J.fst default))).symm
      · simpa [h₂] using! (hc.fac (isPushout.multicofork h h' s) (.right (J.snd default))).symm)⟩

end CategoryTheory.Limits.Multicofork.IsColimit

