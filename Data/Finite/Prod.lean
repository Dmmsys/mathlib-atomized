/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Data.ULift
public import Mathlib.Data.Set.NAry

/-!
# Finiteness of products
-/

public section

assert_not_exists IsOrderedRing MonoidWithZero

variable {α β : Type*}

namespace Finite

/-
**Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] [Finite β] : Finite (α × β) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  infer_instance
/-
**Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β : Sort*} [Finite α] [Finite β] : Finite (PProd α β) :=
  of_equiv _ Equiv.pprodEquivProdPLift.symm
/-
**Finite.prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：prod_left (β) [Finite (α × β)] [Nonempty β] : Finite α
参数：β；α × β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
-/
theorem prod_left (β) [Finite (α × β)] [Nonempty β] : Finite α :=
  of_surjective (Prod.fst : α × β → α) Prod.fst_surjective
/-
**Finite.prod_right** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：prod_right (α) [Finite (α × β)] [Nonempty α] : Finite β
参数：α；α × β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
-/
theorem prod_right (α) [Finite (α × β)] [Nonempty α] : Finite β :=
  of_surjective (Prod.snd : α × β → β) Prod.snd_surjective

end Finite

/-
**Prod.finite_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Prod.finite_iff [Nonempty α] [Nonempty β] : Finite (α × β) ↔ Finite α ∧ Fi
nite β where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.prod_left`：prod_left (β) [Finite (α × β)] [Nonempty β] : Finite α
· 使用定理 `Finite.prod_right`：prod_right (α) [Finite (α × β)] [Nonempty α] : Finite
 β
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
-/
lemma Prod.finite_iff [Nonempty α] [Nonempty β] : Finite (α × β) ↔ Finite α ∧ Finite β where
  mp _ := ⟨.prod_left β, .prod_right α⟩
  mpr | ⟨_, _⟩ => inferInstance
/-
**Pi.finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.finite {α : Sort*} {β : α -> Sort*} [Finite α] [forall a, Finite (β a)]
 : Finite (forall a, β a)
参数：β a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instFinitePLift`：∀ {α : Sort u_1} [Finite α], Finite (PLift α)
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance Pi.finite {α : Sort*} {β : α → Sort*} [Finite α] [∀ a, Finite (β a)] :
    Finite (∀ a, β a) := by
  classical
  have := Fintype.ofFinite (PLift α)
  have := fun a => Fintype.ofFinite (PLift (β a))
  exact
    Finite.of_equiv (∀ a : PLift α, PLift (β (Equiv.plift a)))
      (Equiv.piCongr Equiv.plift fun _ => Equiv.plift)
/-
**Function.Embedding.finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.Embedding.finite {α β : Sort*} [Finite β] : Finite (α ↪ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
instance Function.Embedding.finite {α β : Sort*} [Finite β] : Finite (α ↪ β) := by
  rcases isEmpty_or_nonempty (α ↪ β) with _ | h
  · infer_instance
  · refine h.elim fun f => ?_
    have : Finite α := Finite.of_injective _ f.injective
    exact Finite.of_injective _ DFunLike.coe_injective
/-
**Equiv.finite_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Equiv.finite_right {α β : Sort*} [Finite β] : Finite (α ≃ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
instance Equiv.finite_right {α β : Sort*} [Finite β] : Finite (α ≃ β) :=
  Finite.of_injective Equiv.toEmbedding fun e₁ e₂ h => Equiv.ext <| by
    convert! DFunLike.congr_fun h using 0
/-
**Equiv.finite_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Equiv.finite_left {α β : Sort*} [Finite α] : Finite (α ≃ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.symm = 
e
-/
instance Equiv.finite_left {α β : Sort*} [Finite α] : Finite (α ≃ β) :=
  Finite.of_equiv _ ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩

@[to_additive]
/-
**MulEquiv.finite_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulEquiv.finite_left {α β : Type*} [Mul α] [Mul β] [Finite α] : Finite (α 
≃* β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `MulEquiv.toEquiv_injective`：∀ {α : Type u_9} {β : Type u_10} [inst : Mul
 α] [inst_1 : Mul β], Function.Injective MulEquiv.toEquiv
-/
instance MulEquiv.finite_left {α β : Type*} [Mul α] [Mul β] [Finite α] : Finite (α ≃* β) :=
  Finite.of_injective toEquiv toEquiv_injective

@[to_additive]
/-
**MulEquiv.finite_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulEquiv.finite_right {α β : Type*} [Mul α] [Mul β] [Finite β] : Finite (α
 ≃* β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `MulEquiv.toEquiv_injective`：∀ {α : Type u_9} {β : Type u_10} [inst : Mul
 α] [inst_1 : Mul β], Function.Injective MulEquiv.toEquiv
-/
instance MulEquiv.finite_right {α β : Type*} [Mul α] [Mul β] [Finite β] : Finite (α ≃* β) :=
  Finite.of_injective toEquiv toEquiv_injective

open Set Function

variable {γ : Type*}

namespace Set

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

/-
**Set.fintypeProd** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeProd (s : Set α) (t : Set β) [Fintype s] [Fintype t] : Fintype (s ×
ˢ t : Set (α × β))
参数：s : Set α；t : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeProd (s : Set α) (t : Set β) [Fintype s] [Fintype t] :
    Fintype (s ×ˢ t : Set (α × β)) :=
  Fintype.ofFinset (s.toFinset ×ˢ t.toFinset) <| by simp
/-
**Set.fintypeOffDiag** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeOffDiag (s : Set α) [Fintype s] : Fintype s.offDiag
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeOffDiag (s : Set α) [Fintype s] : Fintype s.offDiag :=
  Fintype.ofFinset s.toFinset.offDiag <| by simp

/-- `image2 f s t` is `Fintype` if `s` and `t` are. -/
/-
**Set.fintypeImage2** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeImage2 [DecidableEq γ] (f : α -> β -> γ) (s : Set α) (t : Set β) [h
s : Fintype s] [ht : Fintype t] : Fintype (image2 f s t : Set γ)
参数：f : α -> β -> γ；s : Set α；t : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`image2 f s t` is `Fintype` if `s` and `t` are.
-/
instance fintypeImage2 [DecidableEq γ] (f : α → β → γ) (s : Set α) (t : Set β) [hs : Fintype s]
    [ht : Fintype t] : Fintype (image2 f s t : Set γ) := by
  rw [← image_prod]
  apply Set.fintypeImage

end FintypeInstances

end Set

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

/-
**Finite.Set.finite_prod** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_prod (s : Set α) (t : Set β) [Finite s] [Finite t] : Finite (s ×ˢ t
 : Set (α × β))
参数：s : Set α；t : Set β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance finite_prod (s : Set α) (t : Set β) [Finite s] [Finite t] :
    Finite (s ×ˢ t : Set (α × β)) :=
  Finite.of_equiv _ (Equiv.Set.prod s t).symm
/-
**Finite.Set.finite_image2** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_image2 (f : α -> β -> γ) (s : Set α) (t : Set β) [Finite s] [Finite
 t] : Finite (image2 f s t : Set γ)
参数：f : α -> β -> γ；s : Set α；t : Set β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
-/
instance finite_image2 (f : α → β → γ) (s : Set α) (t : Set β) [Finite s] [Finite t] :
    Finite (image2 f s t : Set γ) := by
  rw [← image_prod]
  infer_instance

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

section Prod

variable {s : Set α} {t : Set β}

/-
**Set.Finite.prod** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}, s.Finite → t.Fini
te → (s ×ˢ t).Finite
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
protected theorem Finite.prod (hs : s.Finite) (ht : t.Finite) : (s ×ˢ t : Set (α × β)).Finite := by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite
/-
**Set.Finite.of_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}, (s ×ˢ t).Finite →
 t.Nonempty → s.Finite
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
theorem Finite.of_prod_left (h : (s ×ˢ t : Set (α × β)).Finite) : t.Nonempty → s.Finite :=
  fun ⟨b, hb⟩ => (h.image Prod.fst).subset fun a ha => ⟨(a, b), ⟨ha, hb⟩, rfl⟩
/-
**Set.Finite.of_prod_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}, (s ×ˢ t).Finite →
 s.Nonempty → t.Finite
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
theorem Finite.of_prod_right (h : (s ×ˢ t : Set (α × β)).Finite) : s.Nonempty → t.Finite :=
  fun ⟨a, ha⟩ => (h.image Prod.snd).subset fun b hb => ⟨(a, b), ⟨ha, hb⟩, rfl⟩
/-
**Set.Infinite.prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}, s.Infinite → t.No
nempty → (s ×ˢ t).Infinite
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_prod_left`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β}, (s ×ˢ t).Finite → t.Nonempty → s.Finite
-/
protected theorem Infinite.prod_left (hs : s.Infinite) (ht : t.Nonempty) : (s ×ˢ t).Infinite :=
  fun h => hs <| h.of_prod_left ht
/-
**Set.Infinite.prod_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}, t.Infinite → s.No
nempty → (s ×ˢ t).Infinite
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_prod_right`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t
 : Set β}, (s ×ˢ t).Finite → s.Nonempty → t.Finite
-/
protected theorem Infinite.prod_right (ht : t.Infinite) (hs : s.Nonempty) : (s ×ˢ t).Infinite :=
  fun h => ht <| h.of_prod_right hs
/-
**Set.infinite_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β},   (s ×ˢ t).Infini
te ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.Finite.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
, s.Finite → t.Finite → (s ×ˢ t).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Nonempty.snd`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
}, (s ×ˢ t).Nonempty → t.Nonempty
· 使用定理 `Set.Infinite.nonempty`：∀ {α : Type u} {s : Set α}, s.Infinite → s.Nonemp
ty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Nonempty.fst`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
}, (s ×ˢ t).Nonempty → s.Nonempty
· 使用定理 `Set.Infinite.prod_left`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t :
 Set β}, s.Infinite → t.Nonempty → (s ×ˢ t).Infinite
· 使用定理 `Set.Infinite.prod_right`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β}, t.Infinite → s.Nonempty → (s ×ˢ t).Infinite
-/
protected theorem infinite_prod :
    (s ×ˢ t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty := by
  refine ⟨fun h => ?_, ?_⟩
  · simp_rw [Set.Infinite, @and_comm ¬_, ← Classical.not_imp]
    by_contra!
    exact h ((this.1 h.nonempty.snd).prod <| this.2 h.nonempty.fst)
  · rintro (h | h)
    · exact h.1.prod_left h.2
    · exact h.1.prod_right h.2
/-
**Set.finite_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_prod : (s ×ˢ t).Finite ↔ (s.Finite ∨ t = ∅) ∧ (t.Finite ∨ s = ∅)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `Set.infinite_prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set 
β},   (s ×ˢ t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty
-/
theorem finite_prod : (s ×ˢ t).Finite ↔ (s.Finite ∨ t = ∅) ∧ (t.Finite ∨ s = ∅) := by
  contrapose! +distrib; exact Set.infinite_prod
/-
**Set.Finite.offDiag** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, s.Finite → s.offDiag.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
, s.Finite → t.Finite → (s ×ˢ t).Finite
· 使用定理 `Set.offDiag_subset_prod`：offDiag_subset_prod : s.offDiag subseteq s ×ˢ s
-/
protected theorem Finite.offDiag {s : Set α} (hs : s.Finite) : s.offDiag.Finite :=
  (hs.prod hs).subset s.offDiag_subset_prod
/-
**Set.Finite.image2** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {t : Set β} (f 
: α → β → γ),   s.Finite → t.Finite → (Set.image2 f s t).Finite
参数：f : α → β → γ；Set.image2 f s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
protected theorem Finite.image2 (f : α → β → γ) (hs : s.Finite) (ht : t.Finite) :
    (image2 f s t).Finite := by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite

end Prod

end SetFiniteConstructors

/-! ### Properties -/

/-
**Set.Finite.toFinset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} (hs : s.Finite) (h
t : t.Finite),   hs.toFinset ×ˢ ht.toFinset = ⋯.toFinset
参数：hs : s.Finite；ht : t.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Set.Finite.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
, s.Finite → t.Finite → (s ×ˢ t).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
### Properties
-/
theorem Finite.toFinset_prod {s : Set α} {t : Set β} (hs : s.Finite) (ht : t.Finite) :
    hs.toFinset ×ˢ ht.toFinset = (hs.prod ht).toFinset :=
  Finset.ext <| by simp
/-
**Set.Finite.toFinset_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {s : Set α} (hs : s.Finite), ⋯.toFinset = hs.toFinset.off
Diag
参数：hs : s.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Set.Finite.offDiag`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.offDiag.F
inite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Finite.toFinset_offDiag {s : Set α} (hs : s.Finite) :
    hs.offDiag.toFinset = hs.toFinset.offDiag :=
  Finset.ext <| by simp
/-
**Set.finite_image_fst_and_snd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_image_fst_and_snd_iff {s : Set (α × β)} : (Prod.fst '' s).Finite ∧ 
(Prod.snd '' s).Finite ↔ s.Finite
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
, s.Finite → t.Finite → (s ×ˢ t).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
theorem finite_image_fst_and_snd_iff {s : Set (α × β)} :
    (Prod.fst '' s).Finite ∧ (Prod.snd '' s).Finite ↔ s.Finite :=
  ⟨fun h => (h.1.prod h.2).subset fun _ h => ⟨mem_image_of_mem _ h, mem_image_of_mem _ h⟩,
    fun h => ⟨h.image _, h.image _⟩⟩

/-! ### Infinite sets -/

variable {s t : Set α}

section Image2

variable {f : α → β → γ} {s : Set α} {t : Set β} {a : α} {b : β}

/-
**Set.Infinite.image2_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {s : Set α}
 {t : Set β} {b : β},   s.Infinite → b ∈ t → Set.InjOn (fun a => f a b) s → (Set
.image2 f s t).Infinite
参数：fun a => f a b；Set.image2 f s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `Set.image_subset_image2_left`：image_subset_image2_left (hb : b in t) : (
fun a => f a b) '' s subseteq image2 f s t
· 使用定理 `Set.Infinite.image`：∀ {α : Type u} {β : Type v} {s : Set α} {f : α → β},
 Set.InjOn f s → s.Infinite → (f '' s).Infinite
-/
protected theorem Infinite.image2_left (hs : s.Infinite) (hb : b ∈ t)
    (hf : InjOn (fun a => f a b) s) : (image2 f s t).Infinite :=
  (hs.image hf).mono <| image_subset_image2_left hb
/-
**Set.Infinite.image2_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {s : Set α}
 {t : Set β} {a : α},   t.Infinite → a ∈ s → Set.InjOn (f a) t → (Set.image2 f s
 t).Infinite
参数：f a；Set.image2 f s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `Set.image_subset_image2_right`：image_subset_image2_right (ha : a in s) :
 f a '' t subseteq image2 f s t
· 使用定理 `Set.Infinite.image`：∀ {α : Type u} {β : Type v} {s : Set α} {f : α → β},
 Set.InjOn f s → s.Infinite → (f '' s).Infinite
-/
protected theorem Infinite.image2_right (ht : t.Infinite) (ha : a ∈ s) (hf : InjOn (f a) t) :
    (image2 f s t).Infinite :=
  (ht.image hf).mono <| image_subset_image2_right ha
/-
**Set.infinite_image2** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_image2 (hfs : forall b in t, InjOn (fun a => f a b) s) (hft : for
all a in s, InjOn (f a) t) : (image2 f s t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨
 t.Infinite ∧ s.Nonempty
参数：hfs : forall b in t, InjOn (fun a => f a b) s；hft : forall a in s, InjOn (f a
) t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.infinite_prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set 
β},   (s ×ˢ t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty
· 使用定理 `Set.Infinite.of_image`：∀ {α : Type u} {β : Type v} (f : α → β) {s : Set 
α}, (f '' s).Infinite → s.Infinite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_uncurry_prod`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} (
f : α → β → γ) (s : Set α) (t : Set β),   Function.uncurry f '' s ×ˢ t = Set.ima
ge2 f s t
· 使用定理 `Set.Infinite.image2_left`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3}
 {f : α → β → γ} {s : Set α} {t : Set β} {b : β},   s.Infinite → b ∈ t → Set.Inj
On (fun a => f…
· 使用定理 `Set.Infinite.image2_right`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3
} {f : α → β → γ} {s : Set α} {t : Set β} {a : α},   t.Infinite → a ∈ s → Set.In
jOn (f a) t → (…
-/
theorem infinite_image2 (hfs : ∀ b ∈ t, InjOn (fun a => f a b) s) (hft : ∀ a ∈ s, InjOn (f a) t) :
    (image2 f s t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty := by
  refine ⟨fun h => Set.infinite_prod.1 ?_, ?_⟩
  · rw [← image_uncurry_prod] at h
    exact h.of_image _
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact hs.image2_left hb (hfs _ hb)
    · exact ht.image2_right ha (hft _ ha)
/-
**Set.finite_image2** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：finite_image2 (hfs : forall b in t, InjOn (f · b) s) (hft : forall a in s,
 InjOn (f a) t) : (image2 f s t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅
参数：hfs : forall b in t, InjOn (f · b) s；hft : forall a in s, InjOn (f a) t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `Set.infinite_image2`：infinite_image2 (hfs : forall b in t, InjOn (fun a 
=> f a b) s) (hft : forall a in s, InjOn (f a) t) : (image2 f s t).Infinite ↔ s.
Infinite …
-/
lemma finite_image2 (hfs : ∀ b ∈ t, InjOn (f · b) s) (hft : ∀ a ∈ s, InjOn (f a) t) :
    (image2 f s t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ := by
  contrapose! +distrib
  rw [Set.infinite_image2 hfs hft]
  grind only [Set.Infinite.nonempty]

end Image2

end Set

