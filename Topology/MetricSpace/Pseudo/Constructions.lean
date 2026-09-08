/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Bornology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Products of pseudometric spaces and other constructions

This file constructs the supremum distance on binary products of pseudometric spaces and provides
instances for type synonyms.
-/

@[expose] public section

open Bornology Filter Metric Set Topology
open scoped NNReal

variable {α β : Type*} [PseudoMetricSpace α]

/-- Pseudometric space structure pulled back by a function. -/
/-
**PseudoMetricSpace.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PseudoMetricSpace.induced {α β} (f : α -> β) (m : PseudoMetricSpace β) : P
seudoMetricSpace α where dist x y
参数：f : α -> β；m : PseudoMetricSpace β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pseudometric space structure pulled back by a function.
-/
abbrev PseudoMetricSpace.induced {α β} (f : α → β) (m : PseudoMetricSpace β) :
    PseudoMetricSpace α where
  dist x y := dist (f x) (f y)
  dist_self _ := dist_self _
  dist_comm _ _ := dist_comm _ _
  dist_triangle _ _ _ := dist_triangle _ _ _
  edist x y := edist (f x) (f y)
  edist_dist _ _ := edist_dist _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_dist := (uniformity_basis_dist.comap _).eq_biInf
  toBornology := Bornology.induced f
  cobounded_sets := Set.ext fun s => mem_comap_iff_compl.trans <| by
    simp only [← isBounded_def, isBounded_iff, forall_mem_image, mem_ofPred]

/-- Pull back a pseudometric space structure by an inducing map. This is a version of
`PseudoMetricSpace.induced` useful in case if the domain already has a `TopologicalSpace`
structure. -/
@[instance_reducible]
/-
**Topology.IsInducing.comapPseudoMetricSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Topology.IsInducing.comapPseudoMetricSpace {α β : Type*} [TopologicalSpace
 α] [m : PseudoMetricSpace β] {f : α -> β} (hf : IsInducing f) : PseudoMetricSpa
ce α
参数：hf : IsInducing f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a pseudometric space structure by an inducing map. This is a version o
f
`PseudoMetricSpace.induced` useful in case if the domain already has a `Topologi
calSpace`
structure.
-/
def Topology.IsInducing.comapPseudoMetricSpace {α β : Type*} [TopologicalSpace α]
    [m : PseudoMetricSpace β] {f : α → β} (hf : IsInducing f) : PseudoMetricSpace α :=
  .replaceTopology (.induced f m) hf.eq_induced

/-- Pull back a pseudometric space structure by a uniform inducing map. This is a version of
`PseudoMetricSpace.induced` useful in case if the domain already has a `UniformSpace`
structure. -/
@[instance_reducible]
/-
**IsUniformInducing.comapPseudoMetricSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsUniformInducing.comapPseudoMetricSpace {α β} [UniformSpace α] [m : Pseud
oMetricSpace β] (f : α -> β) (h : IsUniformInducing f) : PseudoMetricSpace α
参数：f : α -> β；h : IsUniformInducing f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a pseudometric space structure by a uniform inducing map. This is a ve
rsion of
`PseudoMetricSpace.induced` useful in case if the domain already has a `UniformS
pace`
structure.
-/
def IsUniformInducing.comapPseudoMetricSpace {α β} [UniformSpace α] [m : PseudoMetricSpace β]
    (f : α → β) (h : IsUniformInducing f) : PseudoMetricSpace α :=
  .replaceUniformity (.induced f m) h.comap_uniformity.symm

namespace Subtype

variable {p : α → Prop}

/-
**Subtype.pseudoMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `Subtype`。
形式化陈述：pseudoMetricSpace : PseudoMetricSpace (Subtype p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pseudoMetricSpace : PseudoMetricSpace (Subtype p) :=
  PseudoMetricSpace.induced Subtype.val ‹_›
/-
**Subtype.dist_eq** 是 Mathlib 中的一个引理，位于命名空间 `Subtype`。
形式化陈述：dist_eq (x y : Subtype p) : dist x y = dist (x : α) y
参数：x y : Subtype p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_eq (x y : Subtype p) : dist x y = dist (x : α) y := rfl
/-
**Subtype.nndist_eq** 是 Mathlib 中的一个引理，位于命名空间 `Subtype`。
形式化陈述：nndist_eq (x y : Subtype p) : nndist x y = nndist (x : α) y
参数：x y : Subtype p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nndist_eq (x y : Subtype p) : nndist x y = nndist (x : α) y := rfl

@[simp]
/-
**Subtype.preimage_ball** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：preimage_ball (a : {a // p a}) (r : Real) : Subtype.val ⁻¹' (ball a.1 r) =
 ball a r
参数：a : {a // p a}；r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_ball (a : {a // p a}) (r : ℝ) : Subtype.val ⁻¹' (ball a.1 r) = ball a r :=
  rfl

@[simp]
/-
**Subtype.preimage_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：preimage_closedBall {p : α -> Prop} (a : {a // p a}) (r : Real) : Subtype.
val ⁻¹' (closedBall a.1 r) = closedBall a r
参数：a : {a // p a}；r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_closedBall {p : α → Prop} (a : {a // p a}) (r : ℝ) :
    Subtype.val ⁻¹' (closedBall a.1 r) = closedBall a r :=
  rfl

@[simp]
/-
**Subtype.image_ball** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：image_ball {p : α -> Prop} (a : {a // p a}) (r : Real) : Subtype.val '' (b
all a r) = ball a.1 r inter {a | p a}
参数：a : {a // p a}；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.preimage_ball`：preimage_ball (a : {a // p a}) (r : Real) : Subty
pe.val ⁻¹' (ball a.1 r) = ball a r
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subtype.range_val_subtype`：range_val_subtype {p : α -> Prop} : range (Su
btype.val : Subtype p -> α) = { x | p x }
-/
theorem image_ball {p : α → Prop} (a : {a // p a}) (r : ℝ) :
    Subtype.val '' (ball a r) = ball a.1 r ∩ {a | p a} := by
  rw [← preimage_ball, image_preimage_eq_inter_range, range_val_subtype]

@[simp]
/-
**Subtype.image_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：image_closedBall {p : α -> Prop} (a : {a // p a}) (r : Real) : Subtype.val
 '' (closedBall a r) = closedBall a.1 r inter {a | p a}
参数：a : {a // p a}；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.preimage_closedBall`：preimage_closedBall {p : α -> Prop} (a : {a
 // p a}) (r : Real) : Subtype.val ⁻¹' (closedBall a.1 r) = closedBall a r
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subtype.range_val_subtype`：range_val_subtype {p : α -> Prop} : range (Su
btype.val : Subtype p -> α) = { x | p x }
-/
theorem image_closedBall {p : α → Prop} (a : {a // p a}) (r : ℝ) :
    Subtype.val '' (closedBall a r) = closedBall a.1 r ∩ {a | p a} := by
  rw [← preimage_closedBall, image_preimage_eq_inter_range, range_val_subtype]

end Subtype

namespace MulOpposite

@[to_additive]
/-
**MulOpposite.instPseudoMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instPseudoMetricSpace : PseudoMetricSpace αᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPseudoMetricSpace : PseudoMetricSpace αᵐᵒᵖ :=
  PseudoMetricSpace.induced MulOpposite.unop ‹_›

@[to_additive (attr := simp)]
/-
**MulOpposite.dist_unop** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：dist_unop (x y : αᵐᵒᵖ) : dist (unop x) (unop y) = dist x y
参数：x y : αᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_unop (x y : αᵐᵒᵖ) : dist (unop x) (unop y) = dist x y := rfl

@[to_additive (attr := simp)]
/-
**MulOpposite.dist_op** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：dist_op (x y : α) : dist (op x) (op y) = dist x y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_op (x y : α) : dist (op x) (op y) = dist x y := rfl

@[to_additive (attr := simp)]
/-
**MulOpposite.nndist_unop** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：nndist_unop (x y : αᵐᵒᵖ) : nndist (unop x) (unop y) = nndist x y
参数：x y : αᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nndist_unop (x y : αᵐᵒᵖ) : nndist (unop x) (unop y) = nndist x y := rfl

@[to_additive (attr := simp)]
/-
**MulOpposite.nndist_op** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：nndist_op (x y : α) : nndist (op x) (op y) = nndist x y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nndist_op (x y : α) : nndist (op x) (op y) = nndist x y := rfl

end MulOpposite

section NNReal

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PseudoMetricSpace ℝ≥0 :=
  inferInstanceAs <| PseudoMetricSpace (Subtype _)
/-
**NNReal.dist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NNReal.dist_eq (a b : Real>=0) : dist a b = |(a : Real) - b|
参数：a b : Real>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma NNReal.dist_eq (a b : ℝ≥0) : dist a b = |(a : ℝ) - b| := rfl
/-
**NNReal.nndist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NNReal.nndist_eq (a b : Real>=0) : nndist a b = max (a - b) (b - a)
参数：a b : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma NNReal.nndist_eq (a b : ℝ≥0) : nndist a b = max (a - b) (b - a) :=
  eq_of_forall_ge_iff fun _ => by
    simp only [max_le_iff, tsub_le_iff_right (α := ℝ≥0)]
    simp only [← NNReal.coe_le_coe, coe_nndist, dist_eq, abs_sub_le_iff,
      tsub_le_iff_right, NNReal.coe_add]

@[simp]
/-
**NNReal.nndist_zero_eq_val** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NNReal.nndist_zero_eq_val (z : Real>=0) : nndist 0 z = z
参数：z : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.nndist_eq`：NNReal.nndist_eq (a b : Real>=0) : nndist a b = max (a
 - b) (b - a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma NNReal.nndist_zero_eq_val (z : ℝ≥0) : nndist 0 z = z := by
  simp [NNReal.nndist_eq]

@[simp]
/-
**NNReal.nndist_zero_eq_val'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NNReal.nndist_zero_eq_val' (z : Real>=0) : nndist z 0 = z
参数：z : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nndist_comm`：nndist_comm (x y : α) : nndist x y = nndist y x
· 使用引理 `NNReal.nndist_zero_eq_val`：NNReal.nndist_zero_eq_val (z : Real>=0) : nnd
ist 0 z = z
-/
lemma NNReal.nndist_zero_eq_val' (z : ℝ≥0) : nndist z 0 = z := by
  rw [nndist_comm]
  exact NNReal.nndist_zero_eq_val z
/-
**NNReal.le_add_nndist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NNReal.le_add_nndist (a b : Real>=0) : a <= b + nndist a b
参数：a b : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_of_abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearO
rder G] [IsOrderedAddMonoid G] {a b : G}, |a| ≤ b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `NNReal.dist_eq`：NNReal.dist_eq (a b : Real>=0) : dist a b = |(a : Real) 
- b|
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `NNReal.coe_add`：∀ (r₁ r₂ : NNReal), ↑(r₁ + r₂) = ↑r₁ + ↑r₂
· 使用定理 `coe_nndist`：coe_nndist (x y : α) : ↑(nndist x y) = dist x y
-/
lemma NNReal.le_add_nndist (a b : ℝ≥0) : a ≤ b + nndist a b := by
  suffices (a : ℝ) ≤ (b : ℝ) + dist a b by
    rwa [← NNReal.coe_le_coe, NNReal.coe_add, coe_nndist]
  rw [← sub_le_iff_le_add']
  exact le_of_abs_le (dist_eq a b).ge
/-
**NNReal.ball_zero_eq_Ico'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NNReal.ball_zero_eq_Ico' (c : Real>=0) : Metric.ball (0 : Real>=0) c.toRea
l = Set.Ico 0 c
参数：c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `NNReal.nndist_zero_eq_val'`：NNReal.nndist_zero_eq_val' (z : Real>=0) : n
ndist z 0 = z
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma NNReal.ball_zero_eq_Ico' (c : ℝ≥0) :
    Metric.ball (0 : ℝ≥0) c.toReal = Set.Ico 0 c := by ext x; simp
/-
**NNReal.ball_zero_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NNReal.ball_zero_eq_Ico (c : Real) : Metric.ball (0 : Real>=0) c = Set.Ico
 0 c.toNNReal
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `NNReal.ball_zero_eq_Ico'`：NNReal.ball_zero_eq_Ico' (c : Real>=0) : Metri
c.ball (0 : Real>=0) c.toReal = Set.Ico 0 c
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma NNReal.ball_zero_eq_Ico (c : ℝ) :
    Metric.ball (0 : ℝ≥0) c = Set.Ico 0 c.toNNReal := by
  by_cases! c_pos : 0 < c
  · convert! NNReal.ball_zero_eq_Ico' (NNReal.mk c c_pos.le)
    simp [Real.toNNReal, c_pos.le]
  simp [c_pos]
/-
**NNReal.closedBall_zero_eq_Icc'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NNReal.closedBall_zero_eq_Icc' (c : Real>=0) : Metric.closedBall (0 : Real
>=0) c.toReal = Set.Icc 0 c
参数：c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `NNReal.nndist_zero_eq_val'`：NNReal.nndist_zero_eq_val' (z : Real>=0) : n
ndist z 0 = z
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma NNReal.closedBall_zero_eq_Icc' (c : ℝ≥0) :
    Metric.closedBall (0 : ℝ≥0) c.toReal = Set.Icc 0 c := by ext x; simp
/-
**NNReal.closedBall_zero_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NNReal.closedBall_zero_eq_Icc {c : Real} (c_nn : 0 <= c) : Metric.closedBa
ll (0 : Real>=0) c = Set.Icc 0 c.toNNReal
参数：c_nn : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `NNReal.closedBall_zero_eq_Icc'`：NNReal.closedBall_zero_eq_Icc' (c : Real
>=0) : Metric.closedBall (0 : Real>=0) c.toReal = Set.Icc 0 c
-/
lemma NNReal.closedBall_zero_eq_Icc {c : ℝ} (c_nn : 0 ≤ c) :
    Metric.closedBall (0 : ℝ≥0) c = Set.Icc 0 c.toNNReal := by
  convert! NNReal.closedBall_zero_eq_Icc' (NNReal.mk c c_nn)
  simp [Real.toNNReal, c_nn]

end NNReal

namespace ULift
variable [PseudoMetricSpace β]

/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PseudoMetricSpace (ULift β) :=
  fast_instance% PseudoMetricSpace.induced ULift.down ‹_›
/-
**ULift.dist_eq** 是 Mathlib 中的一个引理，位于命名空间 `ULift`。
形式化陈述：dist_eq (x y : ULift β) : dist x y = dist x.down y.down
参数：x y : ULift β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_eq (x y : ULift β) : dist x y = dist x.down y.down := rfl
/-
**ULift.nndist_eq** 是 Mathlib 中的一个引理，位于命名空间 `ULift`。
形式化陈述：nndist_eq (x y : ULift β) : nndist x y = nndist x.down y.down
参数：x y : ULift β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nndist_eq (x y : ULift β) : nndist x y = nndist x.down y.down := rfl
/-
**ULift.dist_up_up** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {β : Type u_2} [inst : PseudoMetricSpace β] (x y : β), dist { down := x 
} { down := y } = dist x y
参数：x y : β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma dist_up_up (x y : β) : dist (ULift.up x) (ULift.up y) = dist x y := rfl
/-
**ULift.nndist_up_up** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {β : Type u_2} [inst : PseudoMetricSpace β] (x y : β), nndist { down := 
x } { down := y } = nndist x y
参数：x y : β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nndist_up_up (x y : β) : nndist (ULift.up x) (ULift.up y) = nndist x y := rfl

end ULift

section Prod
variable [PseudoMetricSpace β]

/-
**Prod.pseudoMetricSpaceMax** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.pseudoMetricSpaceMax : PseudoMetricSpace (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.pseudoMetricSpaceMax : PseudoMetricSpace (α × β) :=
  let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun x y : α × β => dist x.1 y.1 ⊔ dist x.2 y.2)
    (fun x y ↦ by positivity) fun x y => by
      simp only [ENNReal.ofReal_max, Prod.edist_eq, edist_dist]
  i.replaceBornology fun s => by
    simp only [← isBounded_image_fst_and_snd, isBounded_iff_eventually, forall_mem_image, ←
      eventually_and, ← forall_and, ← max_le_iff]
    rfl
/-
**Prod.dist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Prod.dist_eq {x y : α × β} : dist x y = max (dist x.1 y.1) (dist x.2 y.2)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Prod.dist_eq {x y : α × β} : dist x y = max (dist x.1 y.1) (dist x.2 y.2) := rfl

@[simp]
/-
**dist_prod_same_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_prod_same_left {x : α} {y₁ y₂ : β} : dist (x, y₁) (x, y₂) = dist y₁ y
₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dist_prod_same_left {x : α} {y₁ y₂ : β} : dist (x, y₁) (x, y₂) = dist y₁ y₂ := by
  simp [Prod.dist_eq]

@[simp]
/-
**dist_prod_same_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_prod_same_right {x₁ x₂ : α} {y : β} : dist (x₁, y) (x₂, y) = dist x₁ 
x₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dist_prod_same_right {x₁ x₂ : α} {y : β} : dist (x₁, y) (x₂, y) = dist x₁ x₂ := by
  simp [Prod.dist_eq]
/-
**ball_prod_same** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ball_prod_same (x : α) (y : β) (r : Real) : ball x r ×ˢ ball y r = ball (x
, y) r
参数：x : α；y : β；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ball_prod_same (x : α) (y : β) (r : ℝ) : ball x r ×ˢ ball y r = ball (x, y) r :=
  ext fun z => by simp [Prod.dist_eq]
/-
**closedBall_prod_same** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：closedBall_prod_same (x : α) (y : β) (r : Real) : closedBall x r ×ˢ closed
Ball y r = closedBall (x, y) r
参数：x : α；y : β；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma closedBall_prod_same (x : α) (y : β) (r : ℝ) :
    closedBall x r ×ˢ closedBall y r = closedBall (x, y) r := ext fun z => by simp [Prod.dist_eq]
/-
**sphere_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sphere_prod (x : α × β) (r : Real) : sphere x r = sphere x.1 r ×ˢ closedBa
ll x.2 r union closedBall x.1 r ×ˢ sphere x.2 r
参数：x : α × β；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.sphere_eq_empty_of_neg`：sphere_eq_empty_of_neg (hε : ε < 0) : sph
ere x ε = ∅
· 使用定理 `Metric.closedBall_of_neg`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x
 : α} {ε : ℝ}, ε < 0 → Metric.closedBall x ε = ∅
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.closedBall_eq_sphere_of_nonpos`：closedBall_eq_sphere_of_nonpos (h
ε : ε <= 0) : closedBall x ε = sphere x ε
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `closedBall_prod_same`：closedBall_prod_same (x : α) (y : β) (r : Real) : 
closedBall x r ×ˢ closedBall y r = closedBall (x, y) r
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `or_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `and_congr_left`：∀ {c a b : Prop}, (c → (a ↔ b)) → (a ∧ c ↔ b ∧ c)
-/
lemma sphere_prod (x : α × β) (r : ℝ) :
    sphere x r = sphere x.1 r ×ˢ closedBall x.2 r ∪ closedBall x.1 r ×ˢ sphere x.2 r := by
  obtain hr | rfl | hr := lt_trichotomy r 0
  · simp [hr]
  · cases x
    simp_rw [← closedBall_eq_sphere_of_nonpos le_rfl, union_self, closedBall_prod_same]
  · ext ⟨x', y'⟩
    simp_rw [Set.mem_union, Set.mem_prod, Metric.mem_closedBall, Metric.mem_sphere, Prod.dist_eq,
      max_eq_iff]
    refine or_congr (and_congr_right ?_) (and_comm.trans (and_congr_left ?_))
    all_goals rintro rfl; rfl

end Prod

/-
**uniformContinuous_dist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uniformContinuous_dist : UniformContinuous fun p : α × α => dist p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.uniformContinuous_iff`：uniformContinuous_iff [PseudoMetricSpace β
] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b :
 α⦄, dist a b < δ …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `dist_dist_dist_le`：dist_dist_dist_le (x y x' y' : α) : dist (dist x y) (
dist x' y') <= dist x x' + dist y y'
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma uniformContinuous_dist : UniformContinuous fun p : α × α => dist p.1 p.2 :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, fun {a b} h =>
      calc dist (dist a.1 a.2) (dist b.1 b.2) ≤ dist a.1 b.1 + dist a.2 b.2 :=
        dist_dist_dist_le _ _ _ _
      _ ≤ dist a b + dist a b := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ < ε / 2 + ε / 2 := add_lt_add h h
      _ = ε := add_halves ε⟩
/-
**UniformContinuous.dist** 是 Mathlib 中的一个定理，位于命名空间 `UniformContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpace α] [inst_1 : Uni
formSpace β] {f g : β → α},   UniformContinuous f → UniformContinuous g → Unifor
mContinuous fun b => dist (f b) (g b)
参数：f b；g b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用引理 `uniformContinuous_dist`：uniformContinuous_dist : UniformContinuous fun p
 : α × α => dist p.1 p.2
· 使用定理 `UniformContinuous.prodMk`：UniformContinuous.prodMk {f₁ : α -> β} {f₂ : α
 -> γ} (h₁ : UniformContinuous f₁) (h₂ : UniformContinuous f₂) : UniformContinuo
us fun a => (f…
-/
protected lemma UniformContinuous.dist [UniformSpace β] {f g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun b => dist (f b) (g b) :=
  uniformContinuous_dist.comp (hf.prodMk hg)

@[continuity]
/-
**continuous_dist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_dist : Continuous fun p : α × α => dist p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用引理 `uniformContinuous_dist`：uniformContinuous_dist : UniformContinuous fun p
 : α × α => dist p.1 p.2
-/
lemma continuous_dist : Continuous fun p : α × α ↦ dist p.1 p.2 := uniformContinuous_dist.continuous

@[continuity, fun_prop]
/-
**Continuous.dist** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpace α] [inst_1 : Top
ologicalSpace β] {f g : β → α},   Continuous f → Continuous g → Continuous fun b
 => dist (f b) (g b)
参数：f b；g b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp₂`：Continuous.comp₂ {g : X × Y -> Z} (hg : Continuous g) 
{e : W -> X} (he : Continuous e) {f : W -> Y} (hf : Continuous f) : Continuous f
un w =…
· 使用引理 `continuous_dist`：continuous_dist : Continuous fun p : α × α => dist p.1 
p.2
-/
protected lemma Continuous.dist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => dist (f b) (g b) :=
  continuous_dist.comp₂ hf hg
/-
**Filter.Tendsto.dist** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpace α] {f g : β → α}
 {x : Filter β} {a b : α},   Filter.Tendsto f x (nhds a) →     Filter.Tendsto g 
x (nhds b) → Filter.Tendsto (fun x => dist (f x) (g x)) x (nhds (dist a b))
参数：nhds a；nhds b；fun x => dist (f x) (g x)；nhds (dist a b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用引理 `continuous_dist`：continuous_dist : Continuous fun p : α × α => dist p.1 
p.2
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
protected lemma Filter.Tendsto.dist {f g : β → α} {x : Filter β} {a b : α}
    (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) :
    Tendsto (fun x => dist (f x) (g x)) x (𝓝 (dist a b)) :=
  (continuous_dist.tendsto (a, b)).comp (hf.prodMk_nhds hg)
/-
**continuous_iff_continuous_dist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_iff_continuous_dist [TopologicalSpace β] {f : β -> α} : Continu
ous f ↔ Continuous fun x : β × β => dist (f x.1) (f x.2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `Continuous.fst'`：Continuous.fst' {f : X -> Z} (hf : Continuous f) : Cont
inuous fun x : X × Y => f x.fst
· 使用定理 `Continuous.snd'`：Continuous.snd' {f : Y -> Z} (hf : Continuous f) : Cont
inuous fun x : X × Y => f x.snd
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `tendsto_iff_dist_tendsto_zero`：tendsto_iff_dist_tendsto_zero {f : β -> α
} {x : Filter β} {a : α} : Tendsto f x (𝓝 a) ↔ Tendsto (fun b => dist (f b) a) x
 (𝓝 0)
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.prodMk_left`：Continuous.prodMk_left (y : Y) : Continuous fun 
x : X => (x, y)
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
-/
lemma continuous_iff_continuous_dist [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ Continuous fun x : β × β => dist (f x.1) (f x.2) :=
  ⟨fun h => h.fst'.dist h.snd', fun h =>
    continuous_iff_continuousAt.2 fun _ => tendsto_iff_dist_tendsto_zero.2 <|
      (h.comp (.prodMk_left _)).tendsto' _ _ <| dist_self _⟩
/-
**uniformContinuous_nndist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uniformContinuous_nndist : UniformContinuous fun p : α × α => nndist p.1 p
.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.subtype_mk`：UniformContinuous.subtype_mk {p : α -> Pro
p} [UniformSpace α] [UniformSpace β] {f : β -> α} (hf : UniformContinuous f) (h 
: forall x, p (f x…
· 使用引理 `uniformContinuous_dist`：uniformContinuous_dist : UniformContinuous fun p
 : α × α => dist p.1 p.2
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
lemma uniformContinuous_nndist : UniformContinuous fun p : α × α => nndist p.1 p.2 :=
  uniformContinuous_dist.subtype_mk _
/-
**UniformContinuous.nndist** 是 Mathlib 中的一个定理，位于命名空间 `UniformContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpace α] [inst_1 : Uni
formSpace β] {f g : β → α},   UniformContinuous f → UniformContinuous g → Unifor
mContinuous fun b => nndist (f b) (g b)
参数：f b；g b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用引理 `uniformContinuous_nndist`：uniformContinuous_nndist : UniformContinuous f
un p : α × α => nndist p.1 p.2
· 使用定理 `UniformContinuous.prodMk`：UniformContinuous.prodMk {f₁ : α -> β} {f₂ : α
 -> γ} (h₁ : UniformContinuous f₁) (h₂ : UniformContinuous f₂) : UniformContinuo
us fun a => (f…
-/
protected lemma UniformContinuous.nndist [UniformSpace β] {f g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun b => nndist (f b) (g b) :=
  uniformContinuous_nndist.comp (hf.prodMk hg)
/-
**continuous_nndist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_nndist : Continuous fun p : α × α => nndist p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用引理 `uniformContinuous_nndist`：uniformContinuous_nndist : UniformContinuous f
un p : α × α => nndist p.1 p.2
-/
lemma continuous_nndist : Continuous fun p : α × α => nndist p.1 p.2 :=
  uniformContinuous_nndist.continuous

@[fun_prop]
/-
**Continuous.nndist** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpace α] [inst_1 : Top
ologicalSpace β] {f g : β → α},   Continuous f → Continuous g → Continuous fun b
 => nndist (f b) (g b)
参数：f b；g b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp₂`：Continuous.comp₂ {g : X × Y -> Z} (hg : Continuous g) 
{e : W -> X} (he : Continuous e) {f : W -> Y} (hf : Continuous f) : Continuous f
un w =…
· 使用引理 `continuous_nndist`：continuous_nndist : Continuous fun p : α × α => nndis
t p.1 p.2
-/
protected lemma Continuous.nndist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => nndist (f b) (g b) :=
  continuous_nndist.comp₂ hf hg
/-
**Filter.Tendsto.nndist** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpace α] {f g : β → α}
 {x : Filter β} {a b : α},   Filter.Tendsto f x (nhds a) →     Filter.Tendsto g 
x (nhds b) → Filter.Tendsto (fun x => nndist (f x) (g x)) x (nhds (nndist a b))
参数：nhds a；nhds b；fun x => nndist (f x) (g x)；nhds (nndist a b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用引理 `continuous_nndist`：continuous_nndist : Continuous fun p : α × α => nndis
t p.1 p.2
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
protected lemma Filter.Tendsto.nndist {f g : β → α} {x : Filter β} {a b : α}
    (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) :
    Tendsto (fun x => nndist (f x) (g x)) x (𝓝 (nndist a b)) :=
  (continuous_nndist.tendsto (a, b)).comp (hf.prodMk_nhds hg)
