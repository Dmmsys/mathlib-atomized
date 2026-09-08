/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Ring.Subring.MulOpposite

/-!

# Subalgebras of opposite rings

For every ring `A` over a commutative ring `R`, we construct an equivalence between
subalgebras of `A / R` and that of `Aᵐᵒᵖ / R`.

-/

@[expose] public section

namespace Subalgebra

section Semiring

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Pull a subalgebra back to an opposite subalgebra along `MulOpposite.unop` -/
@[simps! coe toSubsemiring]
/-
**Subalgebra.op** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：{R : Type u_2} →   {A : Type u_3} →     [inst : CommSemiring R] → [inst_1 
: Semiring A] → [inst_2 : Algebra R A] → Subalgebra R A → Subalgebra R Aᵐᵒᵖ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…

--- 原说明 ---
Pull a subalgebra back to an opposite subalgebra along `MulOpposite.unop`
-/
protected def op (S : Subalgebra R A) : Subalgebra R Aᵐᵒᵖ where
  toSubsemiring := S.toSubsemiring.op
  algebraMap_mem' := S.algebraMap_mem

attribute [norm_cast] coe_op

@[simp]
/-
**Subalgebra.mem_op** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_op {x : Aᵐᵒᵖ} {S : Subalgebra R A} : x in S.op ↔ x.unop in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_op {x : Aᵐᵒᵖ} {S : Subalgebra R A} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

/-- Pull a subalgebra back to a subalgebra along `MulOpposite.op` -/
@[simps! coe toSubsemiring]
/-
**Subalgebra.unop** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：{R : Type u_2} →   {A : Type u_3} →     [inst : CommSemiring R] → [inst_1 
: Semiring A] → [inst_2 : Algebra R A] → Subalgebra R Aᵐᵒᵖ → Subalgebra R A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull a subalgebra back to a subalgebra along `MulOpposite.op`
-/
protected def unop (S : Subalgebra R Aᵐᵒᵖ) : Subalgebra R A where
  toSubsemiring := S.toSubsemiring.unop
  algebraMap_mem' := S.algebraMap_mem

attribute [norm_cast] coe_unop

@[simp]
/-
**Subalgebra.mem_unop** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_unop {x : A} {S : Subalgebra R Aᵐᵒᵖ} : x in S.unop ↔ MulOpposite.op x 
in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_unop {x : A} {S : Subalgebra R Aᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[simp]
/-
**Subalgebra.unop_op** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：unop_op (S : Subalgebra R A) : S.op.unop = S
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_op (S : Subalgebra R A) : S.op.unop = S := rfl

@[simp]
/-
**Subalgebra.op_unop** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：op_unop (S : Subalgebra R Aᵐᵒᵖ) : S.unop.op = S
参数：S : Subalgebra R Aᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_unop (S : Subalgebra R Aᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

/-
**Subalgebra.op_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：op_le_iff {S₁ : Subalgebra R A} {S₂ : Subalgebra R Aᵐᵒᵖ} : S₁.op <= S₂ ↔ S
₁ <= S₂.unop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)

--- 原说明 ---
### Lattice results
-/
theorem op_le_iff {S₁ : Subalgebra R A} {S₂ : Subalgebra R Aᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall
/-
**Subalgebra.le_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：le_op_iff {S₁ : Subalgebra R Aᵐᵒᵖ} {S₂ : Subalgebra R A} : S₁ <= S₂.op ↔ S
₁.unop <= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)
-/
theorem le_op_iff {S₁ : Subalgebra R Aᵐᵒᵖ} {S₂ : Subalgebra R A} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
/-
**Subalgebra.op_le_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：op_le_op_iff {S₁ S₂ : Subalgebra R A} : S₁.op <= S₂.op ↔ S₁ <= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)
-/
theorem op_le_op_iff {S₁ S₂ : Subalgebra R A} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
/-
**Subalgebra.unop_le_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：unop_le_unop_iff {S₁ S₂ : Subalgebra R Aᵐᵒᵖ} : S₁.unop <= S₂.unop ↔ S₁ <= 
S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.unop_surjective`：unop_surjective : Surjective (unop : αᵐᵒᵖ -
> α)
-/
theorem unop_le_unop_iff {S₁ S₂ : Subalgebra R Aᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subalgebra `S` of `A / R` determines a subalgebra `S.op` of the opposite ring `Aᵐᵒᵖ / R`. -/
@[simps]
/-
**Subalgebra.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：opEquiv : Subalgebra R A ≃o Subalgebra R Aᵐᵒᵖ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.unop_op`：unop_op (S : Subalgebra R A) : S.op.unop = S
· 使用定理 `Subalgebra.op_unop`：op_unop (S : Subalgebra R Aᵐᵒᵖ) : S.unop.op = S
· 使用定理 `Subalgebra.op_le_op_iff`：op_le_op_iff {S₁ S₂ : Subalgebra R A} : S₁.op <
= S₂.op ↔ S₁ <= S₂

--- 原说明 ---
A subalgebra `S` of `A / R` determines a subalgebra `S.op` of the opposite ring 
`Aᵐᵒᵖ / R`.
-/
def opEquiv : Subalgebra R A ≃o Subalgebra R Aᵐᵒᵖ where
  toFun := Subalgebra.op
  invFun := Subalgebra.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[simp]
/-
**Subalgebra.op_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：op_bot : (⊥ : Subalgebra R A).op = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
-/
theorem op_bot : (⊥ : Subalgebra R A).op = ⊥ := opEquiv.map_bot

@[simp]
/-
**Subalgebra.unop_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：unop_bot : (⊥ : Subalgebra R Aᵐᵒᵖ).unop = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
-/
theorem unop_bot : (⊥ : Subalgebra R Aᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[simp]
/-
**Subalgebra.op_top** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：op_top : (⊤ : Subalgebra R A).op = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_top`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 
: PartialOrder β] [inst_2 : OrderTop α] [inst_3 : OrderTop β]   (f : α ≃o β), f 
⊤ = ⊤
-/
theorem op_top : (⊤ : Subalgebra R A).op = ⊤ := opEquiv.map_top

@[simp]
/-
**Subalgebra.unop_top** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：unop_top : (⊤ : Subalgebra R Aᵐᵒᵖ).unop = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_top`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 
: PartialOrder β] [inst_2 : OrderTop α] [inst_3 : OrderTop β]   (f : α ≃o β), f 
⊤ = ⊤
-/
theorem unop_top : (⊤ : Subalgebra R Aᵐᵒᵖ).unop = ⊤ := opEquiv.symm.map_top
/-
**Subalgebra.op_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：op_sup (S₁ S₂ : Subalgebra R A) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
参数：S₁ S₂ : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem op_sup (S₁ S₂ : Subalgebra R A) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _
/-
**Subalgebra.unop_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：unop_sup (S₁ S₂ : Subalgebra R Aᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
参数：S₁ S₂ : Subalgebra R Aᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem unop_sup (S₁ S₂ : Subalgebra R Aᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _
/-
**Subalgebra.op_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：op_inf (S₁ S₂ : Subalgebra R A) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
参数：S₁ S₂ : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_inf`：OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β]
 (f : α ≃o β) (x y : α) : f (x ⊓ y) = f x ⊓ f y
-/
theorem op_inf (S₁ S₂ : Subalgebra R A) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := opEquiv.map_inf _ _
/-
**Subalgebra.unop_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：unop_inf (S₁ S₂ : Subalgebra R Aᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
参数：S₁ S₂ : Subalgebra R Aᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_inf`：OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β]
 (f : α ≃o β) (x y : α) : f (x ⊓ y) = f x ⊓ f y
-/
theorem unop_inf (S₁ S₂ : Subalgebra R Aᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop :=
  opEquiv.symm.map_inf _ _
/-
**Subalgebra.op_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：op_sSup (S : Set (Subalgebra R A)) : (sSup S).op = sSup (.unop ⁻¹' S)
参数：S : Set (Subalgebra R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sSup_eq_sSup_symm_preimage`：OrderIso.map_sSup_eq_sSup_symm_
preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sSup s) = sSup (f.sym
m ⁻¹' s)
-/
theorem op_sSup (S : Set (Subalgebra R A)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _
/-
**Subalgebra.unop_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：unop_sSup (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S)
参数：S : Set (Subalgebra R Aᵐᵒᵖ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sSup_eq_sSup_symm_preimage`：OrderIso.map_sSup_eq_sSup_symm_
preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sSup s) = sSup (f.sym
m ⁻¹' s)
-/
theorem unop_sSup (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _
/-
**Subalgebra.op_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：op_sInf (S : Set (Subalgebra R A)) : (sInf S).op = sInf (.unop ⁻¹' S)
参数：S : Set (Subalgebra R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sInf_eq_sInf_symm_preimage`：∀ {α : Type u_1} {β : Type u_2}
 [inst : CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β) (s : Set α
),   f (sInf s) = sInf (⇑f.sy…
-/
theorem op_sInf (S : Set (Subalgebra R A)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _
/-
**Subalgebra.unop_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：unop_sInf (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S)
参数：S : Set (Subalgebra R Aᵐᵒᵖ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sInf_eq_sInf_symm_preimage`：∀ {α : Type u_1} {β : Type u_2}
 [inst : CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β) (s : Set α
),   f (sInf s) = sInf (⇑f.sy…
-/
theorem unop_sInf (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _
/-
**Subalgebra.op_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：op_iSup (S : ι -> Subalgebra R A) : (iSup S).op = ⨆ i, (S i).op
参数：S : ι -> Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
theorem op_iSup (S : ι → Subalgebra R A) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _
/-
**Subalgebra.unop_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：unop_iSup (S : ι -> Subalgebra R Aᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop
参数：S : ι -> Subalgebra R Aᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
theorem unop_iSup (S : ι → Subalgebra R Aᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _
/-
**Subalgebra.op_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：op_iInf (S : ι -> Subalgebra R A) : (iInf S).op = ⨅ i, (S i).op
参数：S : ι -> Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
-/
theorem op_iInf (S : ι → Subalgebra R A) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _
/-
**Subalgebra.unop_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：unop_iInf (S : ι -> Subalgebra R Aᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop
参数：S : ι -> Subalgebra R Aᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
-/
theorem unop_iInf (S : ι → Subalgebra R Aᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _
/-
**Subalgebra.op_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：op_adjoin (s : Set A) : (Algebra.adjoin R s).op = Algebra.adjoin R (MulOpp
osite.unop ⁻¹' s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.toSubsemiring_injective`：toSubsemiring_injective : Function.I
njective (toSubsemiring : Subalgebra R A -> Subsemiring A)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.op_toSubsemiring`：∀ {R : Type u_2} {A : Type u_3} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   (S : Subalgebra R A)
, S.op.toSubsemir…
· 使用定理 `Subsemiring.op_closure`：op_closure (s : Set R) : (closure s).op = closur
e (MulOpposite.unop ⁻¹' s)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `MulOpposite.op_unop`：op_unop (x : αᵐᵒᵖ) : op (unop x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem op_adjoin (s : Set A) :
    (Algebra.adjoin R s).op = Algebra.adjoin R (MulOpposite.unop ⁻¹' s) := by
  apply toSubsemiring_injective
  simp_rw [Algebra.adjoin, op_toSubsemiring, Subsemiring.op_closure, Set.preimage_union]
  congr with x
  simp_rw [Set.mem_preimage, Set.mem_range, MulOpposite.algebraMap_apply]
  congr!
  rw [← MulOpposite.op_injective.eq_iff (b := x.unop), MulOpposite.op_unop]
/-
**Subalgebra.unop_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：unop_adjoin (s : Set Aᵐᵒᵖ) : (Algebra.adjoin R s).unop = Algebra.adjoin R 
(MulOpposite.op ⁻¹' s)
参数：s : Set Aᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.toSubsemiring_injective`：toSubsemiring_injective : Function.I
njective (toSubsemiring : Subalgebra R A -> Subsemiring A)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.unop_toSubsemiring`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   (S : Subalgebra R 
Aᵐᵒᵖ), S.unop.toSub…
· 使用定理 `Subsemiring.unop_closure`：unop_closure (s : Set Rᵐᵒᵖ) : (closure s).unop
 = closure (MulOpposite.op ⁻¹' s)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem unop_adjoin (s : Set Aᵐᵒᵖ) :
    (Algebra.adjoin R s).unop = Algebra.adjoin R (MulOpposite.op ⁻¹' s) := by
  apply toSubsemiring_injective
  simp_rw [Algebra.adjoin, unop_toSubsemiring, Subsemiring.unop_closure, Set.preimage_union]
  congr with x
  simp

/-- Bijection between a subalgebra `S` and its opposite. -/
@[simps!]
/-
**Subalgebra.linearEquivOp** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：linearEquivOp (S : Subalgebra R A) : S ≃ₗ[R] S.op where __
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between a subalgebra `S` and its opposite.
-/
def linearEquivOp (S : Subalgebra R A) : S ≃ₗ[R] S.op where
  __ := S.toSubsemiring.addEquivOp
  map_smul' _ _ := rfl

/-- Bijection between a subalgebra `S` and `MulOpposite` of its opposite. -/
@[simps!]
/-
**Subalgebra.algEquivOpMop** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：algEquivOpMop (S : Subalgebra R A) : S ≃ₐ[R] (S.op)ᵐᵒᵖ where __
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between a subalgebra `S` and `MulOpposite` of its opposite.
-/
def algEquivOpMop (S : Subalgebra R A) : S ≃ₐ[R] (S.op)ᵐᵒᵖ where
  __ := S.toSubsemiring.ringEquivOpMop
  commutes' _ := rfl

/-- Bijection between `MulOpposite` of a subalgebra `S` and its opposite. -/
@[simps!]
/-
**Subalgebra.mopAlgEquivOp** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：mopAlgEquivOp (S : Subalgebra R A) : Sᵐᵒᵖ ≃ₐ[R] S.op where __
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between `MulOpposite` of a subalgebra `S` and its opposite.
-/
def mopAlgEquivOp (S : Subalgebra R A) : Sᵐᵒᵖ ≃ₐ[R] S.op where
  __ := S.toSubsemiring.mopRingEquivOp
  commutes' _ := rfl

end Semiring

section Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

@[simp]
/-
**Subalgebra.op_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：op_toSubring (S : Subalgebra R A) : S.op.toSubring = S.toSubring.op
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_toSubring (S : Subalgebra R A) : S.op.toSubring = S.toSubring.op := rfl

@[simp]
/-
**Subalgebra.unop_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：unop_toSubring (S : Subalgebra R Aᵐᵒᵖ) : S.unop.toSubring = S.toSubring.un
op
参数：S : Subalgebra R Aᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_toSubring (S : Subalgebra R Aᵐᵒᵖ) : S.unop.toSubring = S.toSubring.unop := rfl

end Ring

end Subalgebra

