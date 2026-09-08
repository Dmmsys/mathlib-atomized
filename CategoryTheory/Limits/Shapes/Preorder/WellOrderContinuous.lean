/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.PrincipalSeg
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.Order.Interval.Set.InitialSeg
public import Mathlib.Order.Interval.Set.Limit
public import Mathlib.Order.SuccPred.InitialSeg
public import Mathlib.Order.SuccPred.Limit
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Continuity of functors from well-ordered types

Let `F : J ⥤ C` be a functor from a well-ordered type `J`.
We introduce the typeclass `F.IsWellOrderContinuous`
to say that if `m` is a limit element, then `F.obj m`
is the colimit of the `F.obj j` for `j < m`.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory.Functor

open Category Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [PartialOrder J]

/-- A functor `F : J ⥤ C` is well-order-continuous if for any limit element `m : J`,
`F.obj m` identifies to the colimit of the `F.obj j` for `j < m`. -/
/-
**CategoryTheory.Functor.IsWellOrderContinuous** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 w} → [inst_1 : PartialOrder J] → CategoryTheory.Functor J C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : J ⥤ C` is well-order-continuous if for any limit element `m : J`,
`F.obj m` identifies to the colimit of the `F.obj j` for `j < m`.
-/
class IsWellOrderContinuous (F : J ⥤ C) : Prop where
  nonempty_isColimit (m : J) (hm : Order.IsSuccLimit m) :
    Nonempty (IsColimit ((Set.principalSegIio m).cocone F))

/-- If `F : J ⥤ C` is well-order-continuous and `m : J` is a limit element, then
`F.obj m` identifies to the colimit of the `F.obj j` for `j < m`. -/
/-
**CategoryTheory.Functor.isColimitOfIsWellOrderContinuous** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：isColimitOfIsWellOrderContinuous (F : J ⥤ C) [F.IsWellOrderContinuous] (m 
: J) (hm : Order.IsSuccLimit m) : IsColimit ((Set.principalSegIio m).cocone F)
参数：F : J ⥤ C；m : J；hm : Order.IsSuccLimit m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsWellOrderContinuous.nonempty_isColimit`：∀ {C : 
Type u} {inst : CategoryTheory.Category.{v, u} C} {J : Type w} {inst_1 : Partial
Order J}   {F : CategoryTheory.Functor J C} [self : F…

--- 原说明 ---
If `F : J ⥤ C` is well-order-continuous and `m : J` is a limit element, then
`F.obj m` identifies to the colimit of the `F.obj j` for `j < m`.
-/
noncomputable def isColimitOfIsWellOrderContinuous (F : J ⥤ C) [F.IsWellOrderContinuous]
    (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit ((Set.principalSegIio m).cocone F) :=
      (IsWellOrderContinuous.nonempty_isColimit m hm).some

/-- If `F : J ⥤ C` is well-order-continuous and `h : α <i J` is a principal
segment such that `h.top` is a limit element, then
`F.obj h.top` identifies to the colimit of the `F.obj j` for `j : α`. -/
/-
**CategoryTheory.Functor.isColimitOfIsWellOrderContinuous'** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：isColimitOfIsWellOrderContinuous' (F : J ⥤ C) [F.IsWellOrderContinuous] {α
 : Type*} [PartialOrder α] (f : α <i J) (hα : Order.IsSuccLimit f.top) : IsColim
it (f.cocone F)
参数：F : J ⥤ C；f : α <i J；hα : Order.IsSuccLimit f.top。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : J ⥤ C` is well-order-continuous and `h : α <i J` is a principal
segment such that `h.top` is a limit element, then
`F.obj h.top` identifies to the colimit of the `F.obj j` for `j : α`.
-/
noncomputable def isColimitOfIsWellOrderContinuous' (F : J ⥤ C) [F.IsWellOrderContinuous]
    {α : Type*} [PartialOrder α] (f : α <i J) (hα : Order.IsSuccLimit f.top) :
    IsColimit (f.cocone F) :=
  (F.isColimitOfIsWellOrderContinuous f.top hα).whiskerEquivalence
    f.orderIsoIio.equivalence
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : ℕ ⥤ C) : F.IsWellOrderContinuous where
  nonempty_isColimit m hm := by simp at hm
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} (F : Fin n ⥤ C) : F.IsWellOrderContinuous where
  nonempty_isColimit _ hj := (Order.not_isSuccLimit_of_isSuccArchimedean hj).elim

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.isWellOrderContinuous_of_iso** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：isWellOrderContinuous_of_iso {F G : J ⥤ C} (e : F ≅ G) [F.IsWellOrderConti
nuous] : G.IsWellOrderContinuous where nonempty_isColimit (m : J) (hm : Order.Is
SuccLimit m)
参数：e : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalSeg.monotone`：monotone [PartialOrder α] (f : α <i β) : Monotone
 f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma isWellOrderContinuous_of_iso {F G : J ⥤ C} (e : F ≅ G) [F.IsWellOrderContinuous] :
    G.IsWellOrderContinuous where
  nonempty_isColimit (m : J) (hm : Order.IsSuccLimit m) :=
    ⟨(IsColimit.precomposeHomEquiv (isoWhiskerLeft _ e) _).1
      (IsColimit.ofIsoColimit (F.isColimitOfIsWellOrderContinuous m hm)
        (Cocone.ext (e.app _)))⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : J ⥤ C) {J' : Type w'} [PartialOrder J'] (f : J' ≤i J)
    [F.IsWellOrderContinuous] :
    (f.monotone.functor ⋙ F).IsWellOrderContinuous where
  nonempty_isColimit m' hm' := ⟨F.isColimitOfIsWellOrderContinuous'
    ((Set.principalSegIio m').transInitial f) (by simpa)⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : J ⥤ C) {J' : Type w'} [PartialOrder J'] (e : J' ≃o J)
    [F.IsWellOrderContinuous] :
    (e.equivalence.functor ⋙ F).IsWellOrderContinuous :=
  inferInstanceAs (e.toInitialSeg.monotone.functor ⋙ F).IsWellOrderContinuous
/-
**CategoryTheory.Functor.IsWellOrderContinuous.restriction_setIci** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Functor.IsWellOrderContinuous`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [ins
t_1 : LinearOrder J]   {F : CategoryTheory.Functor J C} [F.IsWellOrderContinuous
] (j : J), (⋯.functor.comp F).IsWellOrderContinuous
参数：j : J；⋯.functor.comp F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
· 使用定理 `PrincipalSeg.monotone`：monotone [PartialOrder α] (f : α <i β) : Monotone
 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Monotone.final_functor_iff`：Monotone.final_functor_iff {J₁ J₂ : Type*} [
Preorder J₁] [Preorder J₂] [IsDirectedOrder J₁] {f : J₁ -> J₂} (hf : Monotone f)
 : hf.functor.Fi…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Set.Ici.isSuccLimit_coe`：isSuccLimit_coe {J : Type u} [LinearOrder J] {j
 : J} (m : Set.Ici j) (hm : Order.IsSuccLimit m) : Order.IsSuccLimit m.1
-/
instance IsWellOrderContinuous.restriction_setIci
    {J : Type w} [LinearOrder J]
    {F : J ⥤ C} [F.IsWellOrderContinuous] (j : J) :
    ((Subtype.mono_coe (· ∈ Set.Ici j)).functor ⋙ F).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    let f : Set.Iio m → Set.Iio m.1 := fun ⟨⟨a, ha⟩, ha'⟩ ↦ ⟨a, ha'⟩
    have hf : Monotone f := fun _ _ h ↦ h
    have : hf.functor.Final := by
      rw [Monotone.final_functor_iff]
      rintro ⟨j', hj'⟩
      push _ ∈ _ at hj'
      dsimp only [f]
      by_cases! h : j' ≤ j
      · refine ⟨⟨⟨j, le_refl j⟩, ?_⟩, h⟩
        by_contra h'
        simp only [Set.mem_Iio, not_lt] at h'
        apply hm.1
        rintro ⟨k, hk⟩ hkm
        exact h'.trans hk
      · exact ⟨⟨⟨j', h.le⟩, hj'⟩, by rfl⟩
    exact (Functor.Final.isColimitWhiskerEquiv (F := hf.functor) _).2
      (F.isColimitOfIsWellOrderContinuous m.1 (Set.Ici.isSuccLimit_coe m hm))⟩

end CategoryTheory.Functor

