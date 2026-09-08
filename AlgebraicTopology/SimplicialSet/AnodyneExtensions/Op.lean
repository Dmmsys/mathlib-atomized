/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing

/-!
# The opposite of a pairing

Let `A` be a subcomplex of a simplicial set `X`. If `P` is a pairing of `A`,
we construct a pairing `P.op` for the subcomplex `A.op` of `X.op`.

-/

@[expose] public section

universe u

namespace SSet.Subcomplex.Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)

/-- If `P` is a pairing for a subcomplex `A` of a simplicial set `X`,
this is the corresponding pairing of `A.op`. -/
@[simps I II]
/-
**SSet.Subcomplex.Pairing.op** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.Pairing`
。
形式化陈述：op : A.op.Pairing where I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If `P` is a pairing for a subcomplex `A` of a simplicial set `X`,
this is the corresponding pairing of `A.op`.
-/
def op : A.op.Pairing where
  I := Subcomplex.N.opEquiv ⁻¹' P.I
  II := Subcomplex.N.opEquiv ⁻¹' P.II
  inter := by simp [← Set.preimage_inter, P.inter]
  union := by simp [← Set.preimage_union, P.union]
  p := (N.opEquiv.subtypeEquiv (by simp)).trans
    (P.p.trans (N.opEquiv.symm.subtypeEquiv (by simp)))

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**SSet.Subcomplex.Pairing.op_p** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.Pairin
g`。
形式化陈述：op_p (x : P.II) : dsimp% P.op.p ⟨Subcomplex.N.opEquiv.symm x.1, x.2⟩ = ⟨Su
bcomplex.N.opEquiv.symm (P.p x), by simp⟩
参数：x : P.II。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma op_p (x : P.II) :
    dsimp% P.op.p ⟨Subcomplex.N.opEquiv.symm x.1, x.2⟩ =
      ⟨Subcomplex.N.opEquiv.symm (P.p x), by simp⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**SSet.Subcomplex.Pairing.op_ancestralRel_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Su
bcomplex.Pairing`。
形式化陈述：op_ancestralRel_iff (x y : P.II) : P.op.AncestralRel ⟨Subcomplex.N.opEquiv
.symm x.1, x.2⟩ ⟨Subcomplex.N.opEquiv.symm y.1, y.2⟩ ↔ P.AncestralRel x y
参数：x y : P.II。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma op_ancestralRel_iff (x y : P.II) :
    P.op.AncestralRel ⟨Subcomplex.N.opEquiv.symm x.1, x.2⟩
      ⟨Subcomplex.N.opEquiv.symm y.1, y.2⟩ ↔ P.AncestralRel x y :=
  and_congr (not_congr (by aesop)) (by simp)
/-
**SSet.Subcomplex.Pairing.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.Pairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsProper] : P.op.IsProper where
  isUniquelyCodimOneFace x := (P.isUniquelyCodimOneFace ⟨_, x.2⟩).op
/-
**SSet.Subcomplex.Pairing.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.Pairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsRegular] : P.op.IsRegular where
  wf := by
    have hP := P.wf
    rw [wellFounded_iff_isEmpty_descending_chain] at hP ⊢
    by_contra!
    obtain ⟨f, hf⟩ := this
    refine hP.false ⟨fun n ↦ ⟨_, (f n).2⟩, fun n ↦ ?_⟩
    simpa [← P.op_ancestralRel_iff] using hf n

end SSet.Subcomplex.Pairing

