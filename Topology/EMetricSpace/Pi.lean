/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.UniformSpace.Pi

/-!
# Indexed product of extended metric spaces
-/

@[expose] public section

open Set Filter

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

open scoped Uniformity Topology NNReal ENNReal Pointwise

variable [PseudoEMetricSpace α]

open EMetric

section Pi

open Finset

variable {X : β → Type*} [Fintype β]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ b, EDist (X b)] : EDist (∀ b, X b) where
  edist f g := Finset.sup univ fun b => edist (f b) (g b)
/-
**edist_pi_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_pi_def [forall b, EDist (X b)] (f g : forall b, X b) : edist f g = F
inset.sup univ fun b => edist (f b) (g b)
参数：X b；f g : forall b, X b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_pi_def [∀ b, EDist (X b)] (f g : ∀ b, X b) :
    edist f g = Finset.sup univ fun b => edist (f b) (g b) :=
  rfl
/-
**edist_le_pi_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_pi_edist [forall b, EDist (X b)] (f g : forall b, X b) (b : β) : 
edist (f b) (g b) <= edist f g
参数：X b；f g : forall b, X b；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem edist_le_pi_edist [∀ b, EDist (X b)] (f g : ∀ b, X b) (b : β) :
    edist (f b) (g b) ≤ edist f g :=
  le_sup (f := fun b => edist (f b) (g b)) (Finset.mem_univ b)
/-
**edist_pi_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_pi_le_iff [forall b, EDist (X b)] {f g : forall b, X b} {d : Real>=0
∞} : edist f g <= d ↔ forall b, edist (f b) (g b) <= d
参数：X b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edist_pi_le_iff [∀ b, EDist (X b)] {f g : ∀ b, X b} {d : ℝ≥0∞} :
    edist f g ≤ d ↔ ∀ b, edist (f b) (g b) ≤ d :=
  Finset.sup_le_iff.trans <| by simp only [Finset.mem_univ, forall_const]
/-
**edist_pi_const_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_pi_const_le (a b : α) : (edist (fun _ : β => a) fun _ => b) <= edist
 a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `edist_pi_le_iff`：edist_pi_le_iff [forall b, EDist (X b)] {f g : forall b
, X b} {d : Real>=0∞} : edist f g <= d ↔ forall b, edist (f b) (g b) <= d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem edist_pi_const_le (a b : α) : (edist (fun _ : β => a) fun _ => b) ≤ edist a b :=
  edist_pi_le_iff.2 fun _ => le_rfl

@[simp]
/-
**edist_pi_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_pi_const [Nonempty β] (a b : α) : (edist (fun _ : β => a) fun _ => b
) = edist a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_const`：sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s
.sup fun _ => c) = c
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
-/
theorem edist_pi_const [Nonempty β] (a b : α) : (edist (fun _ : β => a) fun _ => b) = edist a b :=
  Finset.sup_const univ_nonempty (edist a b)

/-- The product of a finite number of pseudoemetric spaces, with the max distance, is still
a pseudoemetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
/-
**pseudoEMetricSpacePi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：pseudoEMetricSpacePi [forall b, PseudoEMetricSpace (X b)] : PseudoEMetricS
pace (forall b, X b) where edist_self f
参数：X b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a finite number of pseudoemetric spaces, with the max distance, i
s still
a pseudoemetric space.
This construction would also work for infinite products, but it would not give r
ise
to the product topology. Hence, we only formalize it in the good situation of fi
nitely many
spaces.
-/
instance pseudoEMetricSpacePi [∀ b, PseudoEMetricSpace (X b)] : PseudoEMetricSpace (∀ b, X b) where
  edist_self f := bot_unique <| Finset.sup_le <| by simp
  edist_comm f g := by simp [edist_pi_def, edist_comm]
  edist_triangle _ g _ := edist_pi_le_iff.2 fun b => le_trans (edist_triangle _ (g b) _)
    (add_le_add (edist_le_pi_edist _ _ _) (edist_le_pi_edist _ _ _))
  toUniformSpace := Pi.uniformSpace _
  uniformity_edist := by
    simp only [Pi.uniformity, PseudoEMetricSpace.uniformity_edist, comap_iInf, gt_iff_lt,
      preimage_ofPred_eq, comap_principal, edist_pi_def]
    rw [iInf_comm]; congr; funext ε
    rw [iInf_comm]; congr; funext εpos
    simp [ofPred_forall, εpos]

end Pi

variable {γ : Type w} [EMetricSpace γ]

section Pi

open Finset

variable {X : β → Type*} [Fintype β]

/-- The product of a finite number of emetric spaces, with the max distance, is still
an emetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
/-
**emetricSpacePi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：emetricSpacePi [forall b, EMetricSpace (X b)] : EMetricSpace (forall b, X 
b)
参数：X b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a finite number of emetric spaces, with the max distance, is stil
l
an emetric space.
This construction would also work for infinite products, but it would not give r
ise
to the product topology. Hence, we only formalize it in the good situation of fi
nitely many
spaces.
-/
instance emetricSpacePi [∀ b, EMetricSpace (X b)] : EMetricSpace (∀ b, X b) :=
  .ofT0PseudoEMetricSpace _

end Pi

