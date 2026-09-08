/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# The complete lattice structure on two-sided ideals
-/

public section

namespace TwoSidedIdeal

variable (R : Type*) [NonUnitalNonAssocRing R]

/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (TwoSidedIdeal R) where
  sup I J := { ringCon := I.ringCon ⊔ J.ringCon }
  le_sup_left I J := by rw [ringCon_le_iff]; exact le_sup_left
  le_sup_right I J := by rw [ringCon_le_iff]; exact le_sup_right
  sup_le I J K h1 h2 := by rw [ringCon_le_iff] at h1 h2 ⊢; exact sup_le h1 h2
/-
**TwoSidedIdeal.sup_ringCon** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：sup_ringCon (I J : TwoSidedIdeal R) : (I ⊔ J).ringCon = I.ringCon ⊔ J.ring
Con
参数：I J : TwoSidedIdeal R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sup_ringCon (I J : TwoSidedIdeal R) : (I ⊔ J).ringCon = I.ringCon ⊔ J.ringCon := rfl

section sup

variable {R}

/-
**TwoSidedIdeal.mem_sup_left** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_sup_left {I J : TwoSidedIdeal R} {x : R} (h : x in I) : x in I ⊔ J
参数：h : x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
lemma mem_sup_left {I J : TwoSidedIdeal R} {x : R} (h : x ∈ I) :
    x ∈ I ⊔ J :=
  (show I ≤ I ⊔ J from le_sup_left) h
/-
**TwoSidedIdeal.mem_sup_right** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_sup_right {I J : TwoSidedIdeal R} {x : R} (h : x in J) : x in I ⊔ J
参数：h : x in J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma mem_sup_right {I J : TwoSidedIdeal R} {x : R} (h : x ∈ J) :
    x ∈ I ⊔ J :=
  (show J ≤ I ⊔ J from le_sup_right) h

set_option backward.isDefEq.respectTransparency false in
/-
**TwoSidedIdeal.mem_sup** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_sup {I J : TwoSidedIdeal R} {x : R} : x in I ⊔ J ↔ exists y in I, exis
ts z in J, y + z = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TwoSidedIdeal.zero_mem`：zero_mem : 0 in I
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `TwoSidedIdeal.add_mem`：add_mem {x y} (hx : x in I) (hy : y in I) : x + y
 in I
· 使用定理 `_private.Mathlib.RingTheory.TwoSidedIdeal.Lattice.0.TwoSidedIdeal.mem_su
p._abel_1_1`：∀ {R : Type u_1} [inst : NonUnitalNonAssocRing R] (x y a b : R), x 
+ a + (y + b) = x + y + (a + b)
· 使用引理 `TwoSidedIdeal.neg_mem`：neg_mem {x} (hx : x in I) : -x in I
· 使用定理 `_private.Mathlib.RingTheory.TwoSidedIdeal.Lattice.0.TwoSidedIdeal.mem_su
p._abel_1_2`：∀ {R : Type u_1} [inst : NonUnitalNonAssocRing R] (x y : R), -x + -
y = -(x + y)
· 使用引理 `TwoSidedIdeal.mul_mem_left`：mul_mem_left (x y) (hy : y in I) : x * y in 
I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用引理 `TwoSidedIdeal.mul_mem_right`：mul_mem_right (x y) (hx : x in I) : x * y i
n I
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TwoSidedIdeal.rel_iff`：rel_iff (x y : R) : I.ringCon x y ↔ x - y in I
· 使用引理 `TwoSidedIdeal.mem_mk'`：mem_mk' (carrier : Set R) (zero_mem add_mem neg_m
em mul_mem_left mul_mem_right) (x : R) : x in mk' carrier zero_mem add_mem neg_m
em mul_mem_…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `TwoSidedIdeal.mem_sup_left`：mem_sup_left {I J : TwoSidedIdeal R} {x : R}
 (h : x in I) : x in I ⊔ J
· 使用引理 `TwoSidedIdeal.mem_sup_right`：mem_sup_right {I J : TwoSidedIdeal R} {x : 
R} (h : x in J) : x in I ⊔ J
-/
lemma mem_sup {I J : TwoSidedIdeal R} {x : R} :
    x ∈ I ⊔ J ↔ ∃ y ∈ I, ∃ z ∈ J, y + z = x := by
  constructor
  · let s : TwoSidedIdeal R := .mk'
      {x | ∃ y ∈ I, ∃ z ∈ J, y + z = x}
      ⟨0, ⟨zero_mem _, ⟨0, ⟨zero_mem _, zero_add _⟩⟩⟩⟩
      (by rintro _ _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩ ⟨a, ⟨ha, ⟨b, ⟨hb, rfl⟩⟩⟩⟩;
          exact ⟨x + a, ⟨add_mem _ hx ha, ⟨y + b, ⟨add_mem _ hy hb, by abel⟩⟩⟩⟩)
      (by rintro _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩
          exact ⟨-x, ⟨neg_mem _ hx, ⟨-y, ⟨neg_mem _ hy, by abel⟩⟩⟩⟩)
      (by rintro r _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩
          exact ⟨_, ⟨mul_mem_left _ _ _ hx, ⟨_, ⟨mul_mem_left _ _ _ hy, mul_add _ _ _ |>.symm⟩⟩⟩⟩)
      (by rintro r _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩
          exact ⟨_, ⟨mul_mem_right _ _ _ hx, ⟨_, ⟨mul_mem_right _ _ _ hy, add_mul _ _ _ |>.symm⟩⟩⟩⟩)
    suffices (I.ringCon ⊔ J.ringCon) ≤ s.ringCon by
      intro h; convert! this h; rw [rel_iff, sub_zero, mem_mk']; rfl
    refine sup_le (fun x y h => ?_) (fun x y h => ?_) <;> rw [rel_iff] at h ⊢ <;> rw [mem_mk']
    exacts [⟨_, ⟨h, ⟨0, ⟨zero_mem _, add_zero _⟩⟩⟩⟩, ⟨0, ⟨zero_mem _, ⟨_, ⟨h, zero_add _⟩⟩⟩⟩]
  · rintro ⟨y, ⟨hy, ⟨z, ⟨hz, rfl⟩⟩⟩⟩; exact add_mem _ (mem_sup_left hy) (mem_sup_right hz)

end sup

/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf (TwoSidedIdeal R) where
  inf I J := { ringCon := I.ringCon ⊓ J.ringCon }
  inf_le_left I J := by rw [ringCon_le_iff]; exact inf_le_left
  inf_le_right I J := by rw [ringCon_le_iff]; exact inf_le_right
  le_inf I J K h1 h2 := by rw [ringCon_le_iff] at h1 h2 ⊢; exact le_inf h1 h2
/-
**TwoSidedIdeal.inf_ringCon** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：inf_ringCon (I J : TwoSidedIdeal R) : (I ⊓ J).ringCon = I.ringCon ⊓ J.ring
Con
参数：I J : TwoSidedIdeal R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inf_ringCon (I J : TwoSidedIdeal R) : (I ⊓ J).ringCon = I.ringCon ⊓ J.ringCon := rfl
/-
**TwoSidedIdeal.mem_inf** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_inf {I J : TwoSidedIdeal R} {x : R} : x in I ⊓ J ↔ x in I ∧ x in J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_inf {I J : TwoSidedIdeal R} {x : R} :
    x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J :=
  Iff.rfl
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SupSet (TwoSidedIdeal R) where
  sSup s := { ringCon := sSup <| TwoSidedIdeal.ringCon '' s }
/-
**TwoSidedIdeal.sSup_ringCon** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：sSup_ringCon (S : Set (TwoSidedIdeal R)) : (sSup S).ringCon = sSup (TwoSid
edIdeal.ringCon '' S)
参数：S : Set (TwoSidedIdeal R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sSup_ringCon (S : Set (TwoSidedIdeal R)) :
    (sSup S).ringCon = sSup (TwoSidedIdeal.ringCon '' S) := rfl
/-
**TwoSidedIdeal.iSup_ringCon** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：iSup_ringCon {ι : Type*} (I : ι -> TwoSidedIdeal R) : (⨆ i, I i).ringCon =
 ⨆ i, (I i).ringCon
参数：I : ι -> TwoSidedIdeal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iSup_ringCon {ι : Type*} (I : ι → TwoSidedIdeal R) :
    (⨆ i, I i).ringCon = ⨆ i, (I i).ringCon := by
  simp only [iSup, sSup_ringCon]; congr; ext; simp
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSemilatticeSup (TwoSidedIdeal R) where
  isLUB_sSup _ := .of_image ringCon_le_iff.symm (isLUB_sSup _)
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (TwoSidedIdeal R) where
  sInf s := { ringCon := sInf <| TwoSidedIdeal.ringCon '' s }
/-
**TwoSidedIdeal.sInf_ringCon** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：sInf_ringCon (S : Set (TwoSidedIdeal R)) : (sInf S).ringCon = sInf (TwoSid
edIdeal.ringCon '' S)
参数：S : Set (TwoSidedIdeal R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sInf_ringCon (S : Set (TwoSidedIdeal R)) :
    (sInf S).ringCon = sInf (TwoSidedIdeal.ringCon '' S) := rfl
/-
**TwoSidedIdeal.iInf_ringCon** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：iInf_ringCon {ι : Type*} (I : ι -> TwoSidedIdeal R) : (⨅ i, I i).ringCon =
 ⨅ i, (I i).ringCon
参数：I : ι -> TwoSidedIdeal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iInf_ringCon {ι : Type*} (I : ι → TwoSidedIdeal R) :
    (⨅ i, I i).ringCon = ⨅ i, (I i).ringCon := by
  simp only [iInf, sInf_ringCon]; congr!; ext; simp
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSemilatticeInf (TwoSidedIdeal R) where
  isGLB_sInf _ := .of_image ringCon_le_iff.symm (isGLB_sInf _)
/-
**TwoSidedIdeal.mem_iInf** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_iInf {ι : Type*} {I : ι -> TwoSidedIdeal R} {x : R} : x in iInf I ↔ fo
rall i, x in I i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_iInf {ι : Type*} {I : ι → TwoSidedIdeal R} {x : R} :
    x ∈ iInf I ↔ ∀ i, x ∈ I i :=
  show (∀ _, _) ↔ _ by simp [mem_iff]
/-
**TwoSidedIdeal.mem_sInf** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_sInf {S : Set (TwoSidedIdeal R)} {x : R} : x in sInf S ↔ forall I in S
, x in I
参数：TwoSidedIdeal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_sInf {S : Set (TwoSidedIdeal R)} {x : R} :
    x ∈ sInf S ↔ ∀ I ∈ S, x ∈ I :=
  show (∀ _, _) ↔ _ by simp [mem_iff]
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (TwoSidedIdeal R) where
  top := { ringCon := ⊤ }
/-
**TwoSidedIdeal.top_ringCon** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：top_ringCon : (⊤ : TwoSidedIdeal R).ringCon = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma top_ringCon : (⊤ : TwoSidedIdeal R).ringCon = ⊤ := rfl

@[simp]
/-
**TwoSidedIdeal.mem_top** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_top {x : R} : x in (⊤ : TwoSidedIdeal R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
lemma mem_top {x : R} : x ∈ (⊤ : TwoSidedIdeal R) := trivial
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (TwoSidedIdeal R) where
  bot := { ringCon := ⊥ }
/-
**TwoSidedIdeal.bot_ringCon** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：bot_ringCon : (⊥ : TwoSidedIdeal R).ringCon = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma bot_ringCon : (⊥ : TwoSidedIdeal R).ringCon = ⊥ := rfl

@[simp]
/-
**TwoSidedIdeal.mem_bot** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_bot {x : R} : x in (⊥ : TwoSidedIdeal R) ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_bot {x : R} : x ∈ (⊥ : TwoSidedIdeal R) ↔ x = 0 :=
  Iff.rfl
/-
**TwoSidedIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (TwoSidedIdeal R) where
  __ := (inferInstance : SemilatticeSup (TwoSidedIdeal R))
  __ := (inferInstance : SemilatticeInf (TwoSidedIdeal R))
  __ := (inferInstance : CompleteSemilatticeSup (TwoSidedIdeal R))
  __ := (inferInstance : CompleteSemilatticeInf (TwoSidedIdeal R))
  le_top _ := by rw [ringCon_le_iff]; exact le_top
  bot_le _ := by rw [ringCon_le_iff]; exact bot_le

@[simp]
/-
**TwoSidedIdeal.coe_bot** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：coe_bot : ((⊥ : TwoSidedIdeal R) : Set R) = {0}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_bot : ((⊥ : TwoSidedIdeal R) : Set R) = {0} := rfl

@[simp]
/-
**TwoSidedIdeal.coe_top** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：coe_top : ((⊤ : TwoSidedIdeal R) : Set R) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_top : ((⊤ : TwoSidedIdeal R) : Set R) = Set.univ := rfl
/-
**TwoSidedIdeal.one_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：one_mem_iff {R : Type*} [NonAssocRing R] (I : TwoSidedIdeal R) : (1 : R) i
n I ↔ I = ⊤
参数：I : TwoSidedIdeal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `TwoSidedIdeal.mul_mem_left`：mul_mem_left (x y) (hy : y in I) : x * y in 
I
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma one_mem_iff {R : Type*} [NonAssocRing R] (I : TwoSidedIdeal R) :
    (1 : R) ∈ I ↔ I = ⊤ :=
  ⟨fun h => eq_top_iff.2 fun x _ => by simpa using I.mul_mem_left x _ h, fun h ↦ h.symm ▸ trivial⟩

alias ⟨eq_top, one_mem⟩ := one_mem_iff

end TwoSidedIdeal

