/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.InitialSeg
public import Mathlib.Order.SuccPred.Limit

/-!
# Initial segments and successors

We establish some connections between initial segment embeddings and successors and predecessors.
-/

public section

variable {α β : Type*} {a b : α} [PartialOrder α] [PartialOrder β]

open Order

namespace InitialSeg

@[simp]
/-
**InitialSeg.apply_covBy_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：apply_covBy_apply_iff (f : α <=i β) : f a ⋖ f b ↔ a ⋖ b
参数：f : α <=i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.apply_covBy_apply_iff`：Set.OrdConnected.apply_covBy_app
ly_iff (f : α ↪o β) (h : (range f).OrdConnected) : f a ⋖ f b ↔ a ⋖ b
· 使用定理 `IsLowerSet.ordConnected`：IsLowerSet.ordConnected (h : IsLowerSet s) : s.
OrdConnected
· 使用定理 `InitialSeg.isLowerSet_range`：isLowerSet_range [LT α] (f : α <=i β) : IsL
owerSet (Set.range f)
-/
theorem apply_covBy_apply_iff (f : α ≤i β) : f a ⋖ f b ↔ a ⋖ b :=
  (isLowerSet_range f).ordConnected.apply_covBy_apply_iff f.toOrderEmbedding

@[simp]
/-
**InitialSeg.apply_wCovBy_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：apply_wCovBy_apply_iff (f : α <=i β) : f a ⩿ f b ↔ a ⩿ b
参数：f : α <=i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InitialSeg.instEmbeddingLike`：∀ {α : Type u_1} {β : Type u_2} {r : α → α
 → Prop} {s : β → β → Prop}, EmbeddingLike (InitialSeg r s) α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem apply_wCovBy_apply_iff (f : α ≤i β) : f a ⩿ f b ↔ a ⩿ b := by
  simp [wcovBy_iff_eq_or_covBy]
/-
**InitialSeg.map_succ** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：map_succ [SuccOrder α] [NoMaxOrder α] [SuccOrder β] (f : α <=i β) (a : α) 
: f (succ a) = succ (f a)
参数：f : α <=i β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CovBy.succ_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : SuccOr
der α] {a b : α}, a ⋖ b → Order.succ a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `InitialSeg.apply_covBy_apply_iff`：apply_covBy_apply_iff (f : α <=i β) : 
f a ⋖ f b ↔ a ⋖ b
· 使用定理 `Order.covBy_succ`：covBy_succ (a : α) : a ⋖ succ a
-/
theorem map_succ [SuccOrder α] [NoMaxOrder α] [SuccOrder β] (f : α ≤i β) (a : α) :
    f (succ a) = succ (f a) :=
  (f.apply_covBy_apply_iff.2 (covBy_succ a)).succ_eq.symm
/-
**InitialSeg.map_pred** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：map_pred [PredOrder α] [NoMinOrder α] [PredOrder β] (f : α <=i β) (a : α) 
: f (pred a) = pred (f a)
参数：f : α <=i β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CovBy.pred_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : PredOr
der α] {a b : α}, b ⋖ a → Order.pred a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `InitialSeg.apply_covBy_apply_iff`：apply_covBy_apply_iff (f : α <=i β) : 
f a ⋖ f b ↔ a ⋖ b
· 使用定理 `Order.pred_covBy`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredOrd
er α] [NoMinOrder α] (a : α), Order.pred a ⋖ a
-/
theorem map_pred [PredOrder α] [NoMinOrder α] [PredOrder β] (f : α ≤i β) (a : α) :
    f (pred a) = pred (f a) :=
  (f.apply_covBy_apply_iff.2 (pred_covBy a)).pred_eq.symm

@[simp]
/-
**InitialSeg.isSuccPrelimit_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：isSuccPrelimit_apply_iff (f : α <=i β) : IsSuccPrelimit (f a) ↔ IsSuccPrel
imit a
参数：f : α <=i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InitialSeg.apply_covBy_apply_iff`：apply_covBy_apply_iff (f : α <=i β) : 
f a ⋖ f b ↔ a ⋖ b
· 使用定理 `InitialSeg.mem_range_of_rel`：mem_range_of_rel (f : r ≼i s) {a : α} {b : 
β} : s b (f a) -> b in Set.range f
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
-/
theorem isSuccPrelimit_apply_iff (f : α ≤i β) : IsSuccPrelimit (f a) ↔ IsSuccPrelimit a := by
  constructor <;> intro h b hb
  · rw [← f.apply_covBy_apply_iff] at hb
    exact h _ hb
  · obtain ⟨c, rfl⟩ := f.mem_range_of_rel hb.lt
    rw [f.apply_covBy_apply_iff] at hb
    exact h _ hb

@[simp]
/-
**InitialSeg.isSuccLimit_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：isSuccLimit_apply_iff (f : α <=i β) : IsSuccLimit (f a) ↔ IsSuccLimit a
参数：f : α <=i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSuccLimit_apply_iff (f : α ≤i β) : IsSuccLimit (f a) ↔ IsSuccLimit a := by
  simp [isSuccLimit_iff]

alias ⟨_, map_isSuccPrelimit⟩ := isSuccPrelimit_apply_iff
alias ⟨_, map_isSuccLimit⟩ := isSuccLimit_apply_iff

end InitialSeg

namespace PrincipalSeg

@[simp]
/-
**PrincipalSeg.apply_covBy_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：apply_covBy_apply_iff (f : α <i β) : f a ⋖ f b ↔ a ⋖ b
参数：f : α <i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.apply_covBy_apply_iff`：apply_covBy_apply_iff (f : α <=i β) : 
f a ⋖ f b ↔ a ⋖ b
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem apply_covBy_apply_iff (f : α <i β) : f a ⋖ f b ↔ a ⋖ b :=
  (f : α ≤i β).apply_covBy_apply_iff

@[simp]
/-
**PrincipalSeg.apply_wCovBy_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：apply_wCovBy_apply_iff (f : α <i β) : f a ⩿ f b ↔ a ⩿ b
参数：f : α <i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.apply_wCovBy_apply_iff`：apply_wCovBy_apply_iff (f : α <=i β) 
: f a ⩿ f b ↔ a ⩿ b
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem apply_wCovBy_apply_iff (f : α <i β) : f a ⩿ f b ↔ a ⩿ b :=
  (f : α ≤i β).apply_wCovBy_apply_iff
/-
**PrincipalSeg.map_succ** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：map_succ [SuccOrder α] [NoMaxOrder α] [SuccOrder β] (f : α <i β) (a : α) :
 f (succ a) = succ (f a)
参数：f : α <i β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.map_succ`：map_succ [SuccOrder α] [NoMaxOrder α] [SuccOrder β]
 (f : α <=i β) (a : α) : f (succ a) = succ (f a)
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem map_succ [SuccOrder α] [NoMaxOrder α] [SuccOrder β] (f : α <i β) (a : α) :
    f (succ a) = succ (f a) :=
  (f : α ≤i β).map_succ a
/-
**PrincipalSeg.map_pred** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：map_pred [PredOrder α] [NoMinOrder α] [PredOrder β] (f : α <=i β) (a : α) 
: f (pred a) = pred (f a)
参数：f : α <=i β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.map_pred`：map_pred [PredOrder α] [NoMinOrder α] [PredOrder β]
 (f : α <=i β) (a : α) : f (pred a) = pred (f a)
-/
theorem map_pred [PredOrder α] [NoMinOrder α] [PredOrder β] (f : α ≤i β) (a : α) :
    f (pred a) = pred (f a) :=
  (f : α ≤i β).map_pred a

@[simp]
/-
**PrincipalSeg.isSuccPrelimit_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`
。
形式化陈述：isSuccPrelimit_apply_iff (f : α <i β) : IsSuccPrelimit (f a) ↔ IsSuccPreli
mit a
参数：f : α <i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.isSuccPrelimit_apply_iff`：isSuccPrelimit_apply_iff (f : α <=i
 β) : IsSuccPrelimit (f a) ↔ IsSuccPrelimit a
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem isSuccPrelimit_apply_iff (f : α <i β) : IsSuccPrelimit (f a) ↔ IsSuccPrelimit a :=
  (f : α ≤i β).isSuccPrelimit_apply_iff

@[simp]
/-
**PrincipalSeg.isSuccLimit_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：isSuccLimit_apply_iff (f : α <i β) : IsSuccLimit (f a) ↔ IsSuccLimit a
参数：f : α <i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.isSuccLimit_apply_iff`：isSuccLimit_apply_iff (f : α <=i β) : 
IsSuccLimit (f a) ↔ IsSuccLimit a
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem isSuccLimit_apply_iff (f : α <i β) : IsSuccLimit (f a) ↔ IsSuccLimit a :=
  (f : α ≤i β).isSuccLimit_apply_iff

alias ⟨_, map_isSuccPrelimit⟩ := isSuccPrelimit_apply_iff
alias ⟨_, map_isSuccLimit⟩ := isSuccLimit_apply_iff

end PrincipalSeg

