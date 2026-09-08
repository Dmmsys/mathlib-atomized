/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Multiequalizers in Type

Given `J : MulticospanShape` and `I : MulticospanIndex J (Type u)`,
we define a type `I.sections`. When `c : Multifork I`, we show
that `c` is a limit iff the canonical map
`c.toSections : c.pt → I.sections` is a bijection.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {J : MulticospanShape} (I : MulticospanIndex J (Type u))

/-- Given `I : MulticospanIndex J (Type u)`, this is a type which identifies
to the sections of the functor `I.multicospan`. -/
@[ext]
/-
**CategoryTheory.Limits.MulticospanIndex.sections** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.Limits.MulticospanIndex`。
形式化陈述：{J : CategoryTheory.Limits.MulticospanShape} → CategoryTheory.Limits.Multi
cospanIndex J (Type u) → Type (max u u_1)
参数：Type u；max u u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `I : MulticospanIndex J (Type u)`, this is a type which identifies
to the sections of the functor `I.multicospan`.
-/
structure MulticospanIndex.sections where
  /-- The data of an element in `I.left i` for each `i : J.L`. -/
  val (i : J.L) : I.left i
  property (r : J.R) : I.fst r (val _) = I.snd r (val _)

/-- The bijection `I.sections ≃ I.multicospan.sections` when `I : MulticospanIndex (Type u)`
is a multiequalizer diagram in the category of types. -/
@[simps]
/-
**CategoryTheory.Limits.MulticospanIndex.sectionsEquiv** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：{J : CategoryTheory.Limits.MulticospanShape} →   (I : CategoryTheory.Limit
s.MulticospanIndex J (Type u)) → I.sections ≃ ↑I.multicospan.sections
参数：I : CategoryTheory.Limits.MulticospanIndex J (Type u)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `I.sections ≃ I.multicospan.sections` when `I : MulticospanIndex (
Type u)`
is a multiequalizer diagram in the category of types.
-/
def MulticospanIndex.sectionsEquiv :
    I.sections ≃ I.multicospan.sections where
  toFun s :=
    { val := fun i ↦ match i with
        | .left i => s.val i
        | .right j => I.fst j (s.val _)
      property := by
        rintro _ _ (_ | _ | r)
        · rfl
        · rfl
        · exact (s.property r).symm }
  invFun s :=
    { val := fun i ↦ s.val (.left i)
      property := fun r ↦ (s.property (.fst r)).trans (s.property (.snd r)).symm }
  right_inv s := by
    ext (_ | r)
    · rfl
    · exact s.property (.fst r)

namespace Multifork

variable {I}
variable (c : Multifork I)

/-- Given a multiequalizer diagram `I : MulticospanIndex (Type u)` in the category of
types and `c` a multifork for `I`, this is the canonical map `c.pt → I.sections`. -/
@[simps]
/-
**CategoryTheory.Limits.Multifork.toSections** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.Multifork`。
形式化陈述：toSections (x : c.pt) : I.sections where val i
参数：x : c.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a multiequalizer diagram `I : MulticospanIndex (Type u)` in the category o
f
types and `c` a multifork for `I`, this is the canonical map `c.pt → I.sections`
.
-/
def toSections (x : c.pt) : I.sections where
  val i := c.ι i x
  property r := ConcreteCategory.congr_hom (c.condition r) x
/-
**CategoryTheory.Limits.Multifork.toSections_fac** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits.Multifork`。
形式化陈述：toSections_fac : I.sectionsEquiv.symm ∘ Types.sectionOfCone c = c.toSectio
ns
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma toSections_fac : I.sectionsEquiv.symm ∘ Types.sectionOfCone c = c.toSections := rfl

/-- A multifork `c : Multifork I` in the category of types is limit iff the
map `c.toSections : c.pt → I.sections` is a bijection. -/
/-
**CategoryTheory.Limits.Multifork.isLimit_types_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits.Multifork`。
形式化陈述：isLimit_types_iff : Nonempty (IsLimit c) ↔ Function.Bijective c.toSections
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.isLimit_iff_bijective_sectionOfCone`：isLimit
_iff_bijective_sectionOfCone (c : Cone F) : Nonempty (IsLimit c) ↔ (Types.sectio
nOfCone c).Bijective
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.Multifork.toSections_fac`：toSections_fac : I.secti
onsEquiv.symm ∘ Types.sectionOfCone c = c.toSections
· 使用定理 `EquivLike.comp_bijective`：comp_bijective (f : α -> β) (e : F) : Function
.Bijective (e ∘ f) ↔ Function.Bijective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A multifork `c : Multifork I` in the category of types is limit iff the
map `c.toSections : c.pt → I.sections` is a bijection.
-/
lemma isLimit_types_iff : Nonempty (IsLimit c) ↔ Function.Bijective c.toSections := by
  rw [Types.isLimit_iff_bijective_sectionOfCone, ← toSections_fac, EquivLike.comp_bijective]

namespace IsLimit

variable {c} (hc : IsLimit c)

/-- The bijection `I.sections ≃ c.pt` when `c : Multifork I` is a limit multifork
in the category of types. -/
/-
**CategoryTheory.Limits.Multifork.IsLimit.sectionsEquiv** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.Multifork.IsLimit`。
形式化陈述：sectionsEquiv : I.sections ≃ c.pt
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The bijection `I.sections ≃ c.pt` when `c : Multifork I` is a limit multifork
in the category of types.
-/
noncomputable def sectionsEquiv : I.sections ≃ c.pt :=
  (Equiv.ofBijective _ (c.isLimit_types_iff.1 ⟨hc⟩)).symm

@[simp]
/-
**CategoryTheory.Limits.Multifork.IsLimit.sectionsEquiv_symm_apply_val** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Limits.Multifork.IsLimit`。
形式化陈述：sectionsEquiv_symm_apply_val (x : c.pt) (i : J.L) : ((sectionsEquiv hc).sy
mm x).val i = c.ι i x
参数：x : c.pt；i : J.L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma sectionsEquiv_symm_apply_val (x : c.pt) (i : J.L) :
    ((sectionsEquiv hc).symm x).val i = c.ι i x := rfl

@[simp]
/-
**CategoryTheory.Limits.Multifork.IsLimit.sectionsEquiv_apply_val** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Limits.Multifork.IsLimit`。
形式化陈述：sectionsEquiv_apply_val (s : I.sections) (i : J.L) : c.ι i (sectionsEquiv 
hc s) = s.val i
参数：s : I.sections；i : J.L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sectionsEquiv_apply_val (s : I.sections) (i : J.L) :
    c.ι i (sectionsEquiv hc s) = s.val i := by
  obtain ⟨x, rfl⟩ := (sectionsEquiv hc).symm.surjective s
  simp

end IsLimit

end Multifork

end CategoryTheory.Limits

