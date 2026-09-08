/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Order.Directed
public import Mathlib.Order.RelIso.Basic
public import Mathlib.Logic.Embedding.Set
public import Mathlib.Logic.Equiv.Set

/-!
# Interactions between relation homomorphisms and sets

It is likely that there are better homes for many of these statement,
in files further down the import graph.
-/

@[expose] public section


open Function

universe u v w

variable {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}

namespace RelHomClass

variable {F : Type*}

/-
**RelHomClass.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `RelHomClass`。
形式化陈述：map_inf [SemilatticeInf α] [LinearOrder β] [FunLike F β α] [RelHomClass F 
(· < ·) (· < ·)] (a : F) (m n : β) : a (m ⊓ n) = a m ⊓ a n
参数：· < ·；· < ·；a : F；m n : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (min x y) = 
f x ⊓ …
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `RelHomClass.map_rel`：∀ {F : Type u_5} {α : outParam (Type u_6)} {β : out
Param (Type u_7)} {r : outParam (α → α → Prop)}   {s : outParam (β → β → Prop)} 
{inst : F…
-/
theorem map_inf [SemilatticeInf α] [LinearOrder β] [FunLike F β α]
    [RelHomClass F (· < ·) (· < ·)] (a : F) (m n : β) :
    a (m ⊓ n) = a m ⊓ a n :=
  (StrictMono.monotone fun _ _ => map_rel a).map_inf m n
/-
**RelHomClass.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `RelHomClass`。
形式化陈述：map_sup [SemilatticeSup α] [LinearOrder β] [FunLike F β α] [RelHomClass F 
(· > ·) (· > ·)] (a : F) (m n : β) : a (m ⊔ n) = a m ⊔ a n
参数：· > ·；· > ·；a : F；m n : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.map_inf`：map_inf [SemilatticeInf α] [LinearOrder β] [FunLike
 F β α] [RelHomClass F (· < ·) (· < ·)] (a : F) (m n : β) : a (m ⊓ n) = a m ⊓ a 
n
-/
theorem map_sup [SemilatticeSup α] [LinearOrder β] [FunLike F β α]
    [RelHomClass F (· > ·) (· > ·)] (a : F) (m n : β) :
    a (m ⊔ n) = a m ⊔ a n :=
  map_inf (α := αᵒᵈ) (β := βᵒᵈ) _ _ _
/-
**RelHomClass.directed** 是 Mathlib 中的一个定理，位于命名空间 `RelHomClass`。
形式化陈述：directed [FunLike F α β] [RelHomClass F r s] {ι : Sort*} {a : ι -> α} {f :
 F} (ha : Directed r a) : Directed s (f ∘ a)
参数：ha : Directed r a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Directed.mono_comp`：Directed.mono_comp (r : α -> α -> Prop) {ι} {rb : β 
-> β -> Prop} {g : α -> β} {f : ι -> α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g
 y)) (hf…
· 使用定理 `RelHomClass.map_rel`：∀ {F : Type u_5} {α : outParam (Type u_6)} {β : out
Param (Type u_7)} {r : outParam (α → α → Prop)}   {s : outParam (β → β → Prop)} 
{inst : F…
-/
theorem directed [FunLike F α β] [RelHomClass F r s] {ι : Sort*} {a : ι → α} {f : F}
    (ha : Directed r a) : Directed s (f ∘ a) :=
  ha.mono_comp _ fun _ _ h ↦ map_rel f h
/-
**RelHomClass.directedOn** 是 Mathlib 中的一个定理，位于命名空间 `RelHomClass`。
形式化陈述：directedOn [FunLike F α β] [RelHomClass F r s] {f : F} {t : Set α} (hs : D
irectedOn r t) : DirectedOn s (f '' t)
参数：hs : DirectedOn r t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.mono_comp`：DirectedOn.mono_comp {r : α -> α -> Prop} {rb : β 
-> β -> Prop} {g : α -> β} {s : Set α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g 
y)) (hf : …
· 使用定理 `RelHomClass.map_rel`：∀ {F : Type u_5} {α : outParam (Type u_6)} {β : out
Param (Type u_7)} {r : outParam (α → α → Prop)}   {s : outParam (β → β → Prop)} 
{inst : F…
-/
theorem directedOn [FunLike F α β] [RelHomClass F r s] {f : F}
    {t : Set α} (hs : DirectedOn r t) : DirectedOn s (f '' t) :=
  hs.mono_comp fun _ _ h ↦ map_rel f h

end RelHomClass

namespace RelIso

/-
**RelIso.range_eq** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：range_eq (e : r ≃r s) : Set.range e = Set.univ
参数：e : r ≃r s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_eq (e : r ≃r s) : Set.range e = Set.univ := by simp

end RelIso

/-- `Subrel r p` is the inherited relation on a subtype.

We could also consider a Set.Subrel r s variant for dot notation, but this ends up interacting
poorly with `simpNF`. -/
/-
**Subrel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subrel (r : α -> α -> Prop) (p : α -> Prop) : Subtype p -> Subtype p -> Pr
op
参数：r : α -> α -> Prop；p : α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subrel r p` is the inherited relation on a subtype.

We could also consider a Set.Subrel r s variant for dot notation, but this ends 
up interacting
poorly with `simpNF`.
-/
def Subrel (r : α → α → Prop) (p : α → Prop) : Subtype p → Subtype p → Prop :=
  Subtype.val ⁻¹'o r

@[simp]
/-
**subrel_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subrel_val (r : α -> α -> Prop) (p : α -> Prop) {a b} : Subrel r p a b ↔ r
 a.1 b.1
参数：r : α -> α -> Prop；p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subrel_val (r : α → α → Prop) (p : α → Prop) {a b} : Subrel r p a b ↔ r a.1 b.1 :=
  Iff.rfl

namespace Subrel

/-- The relation embedding from the inherited relation on a subset. -/
/-
**Subrel.relEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Subrel`。
形式化陈述：{α : Type u_1} → (r : α → α → Prop) → (p : α → Prop) → Subrel r p ↪r r
参数：r : α → α → Prop；p : α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation embedding from the inherited relation on a subset.
-/
protected def relEmbedding (r : α → α → Prop) (p : α → Prop) : Subrel r p ↪r r :=
  ⟨Embedding.subtype _, Iff.rfl⟩

@[simp]
/-
**Subrel.relEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subrel`。
形式化陈述：relEmbedding_apply (r : α -> α -> Prop) (p a) : Subrel.relEmbedding r p a 
= a.1
参数：r : α -> α -> Prop；p a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem relEmbedding_apply (r : α → α → Prop) (p a) : Subrel.relEmbedding r p a = a.1 :=
  rfl

/-- `Set.inclusion` as a relation embedding. -/
/-
**Subrel.inclusionEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Subrel`。
形式化陈述：{α : Type u_1} → (r : α → α → Prop) → {s t : Set α} → s ⊆ t → (Subrel r fu
n x => x ∈ s) ↪r Subrel r fun x => x ∈ t
参数：r : α → α → Prop；Subrel r fun x => x ∈ s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Set.inclusion` as a relation embedding.
-/
protected def inclusionEmbedding (r : α → α → Prop) {s t : Set α} (h : s ⊆ t) :
    Subrel r (· ∈ s) ↪r Subrel r (· ∈ t) where
  toFun := Set.inclusion h
  inj' _ _ h := (Set.inclusion_inj _).mp h
  map_rel_iff' := Iff.rfl

@[simp]
/-
**Subrel.coe_inclusionEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Subrel`。
形式化陈述：coe_inclusionEmbedding (r : α -> α -> Prop) {s t : Set α} (h : s subseteq 
t) : (Subrel.inclusionEmbedding r h : s -> t) = Set.inclusion h
参数：r : α -> α -> Prop；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inclusionEmbedding (r : α → α → Prop) {s t : Set α} (h : s ⊆ t) :
    (Subrel.inclusionEmbedding r h : s → t) = Set.inclusion h :=
  rfl
/-
**Subrel.** 是 Mathlib 中的一个实例，位于命名空间 `Subrel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [Std.Refl r] (p : α → Prop) : Std.Refl (Subrel r p) :=
  ⟨fun x => Std.Refl.refl (r := r) x⟩
/-
**Subrel.** 是 Mathlib 中的一个实例，位于命名空间 `Subrel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [Std.Symm r] (p : α → Prop) : Std.Symm (Subrel r p) :=
  ⟨fun x y => Std.Symm.symm (r := r) x y⟩
/-
**Subrel.** 是 Mathlib 中的一个实例，位于命名空间 `Subrel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [Std.Asymm r] (p : α → Prop) : Std.Asymm (Subrel r p) :=
  ⟨fun x y => Std.Asymm.asymm (r := r) x y⟩
/-
**Subrel.** 是 Mathlib 中的一个实例，位于命名空间 `Subrel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [IsTrans α r] (p : α → Prop) : IsTrans _ (Subrel r p) :=
  ⟨fun x y z => IsTrans.trans (r := r) x y z⟩
/-
**Subrel.** 是 Mathlib 中的一个实例，位于命名空间 `Subrel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [Std.Irrefl r] (p : α → Prop) : Std.Irrefl (Subrel r p) :=
  ⟨fun x => Std.Irrefl.irrefl (r := r) x⟩
/-
**Subrel.** 是 Mathlib 中的一个实例，位于命名空间 `Subrel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [Std.Trichotomous r] (p : α → Prop) : Std.Trichotomous (Subrel r p) :=
  ⟨fun x y => by rw [Subtype.ext_iff]; exact @Std.Trichotomous.trichotomous α r _ x y⟩
/-
**Subrel.** 是 Mathlib 中的一个实例，位于命名空间 `Subrel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [IsWellFounded α r] (p : α → Prop) : IsWellFounded _ (Subrel r p) :=
  (Subrel.relEmbedding r p).isWellFounded
/-
**Subrel.** 是 Mathlib 中的一个实例，位于命名空间 `Subrel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [IsPreorder α r] (p : α → Prop) : IsPreorder _ (Subrel r p) where
/-
**Subrel.** 是 Mathlib 中的一个实例，位于命名空间 `Subrel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [IsStrictOrder α r] (p : α → Prop) : IsStrictOrder _ (Subrel r p) where
/-
**Subrel.** 是 Mathlib 中的一个实例，位于命名空间 `Subrel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [IsWellOrder α r] (p : α → Prop) : IsWellOrder _ (Subrel r p) where

end Subrel

/-- If a proposition holds for all elements, then the `Subrel` is equivalent to the original
relation. -/
@[simps! apply symm_apply]
/-
**RelIso.subrelUnivIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RelIso.subrelUnivIso {p : α -> Prop} (h : forall x, p x) : Subrel r p ≃r r
 where toEquiv
参数：h : forall x, p x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a proposition holds for all elements, then the `Subrel` is equivalent to the 
original
relation.
-/
def RelIso.subrelUnivIso {p : α → Prop} (h : ∀ x, p x) : Subrel r p ≃r r where
  toEquiv := Equiv.subtypeUnivEquiv h
  map_rel_iff' := by simp

/-- Restrict the codomain of a relation embedding. -/
/-
**RelEmbedding.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RelEmbedding.codRestrict (p : Set β) (f : r ↪r s) (H : forall a, f a in p)
 : r ↪r Subrel s (· in p)
参数：p : Set β；f : r ↪r s；H : forall a, f a in p。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.map_rel_iff'`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → 
Prop} {s : β → β → Prop} (self : r ↪r s) {a b : α},   s (self.toEmbedding a) (se
lf.toEmbedding …

--- 原说明 ---
Restrict the codomain of a relation embedding.
-/
def RelEmbedding.codRestrict (p : Set β) (f : r ↪r s) (H : ∀ a, f a ∈ p) : r ↪r Subrel s (· ∈ p) :=
  ⟨f.toEmbedding.codRestrict p H, f.map_rel_iff'⟩

@[simp]
/-
**RelEmbedding.codRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelEmbedding.codRestrict_apply (p) (f : r ↪r s) (H a) : RelEmbedding.codRe
strict p f H a = ⟨f a, H a⟩
参数：p；f : r ↪r s；H a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelEmbedding.codRestrict_apply (p) (f : r ↪r s) (H a) :
    RelEmbedding.codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl

section image

/-
**RelIso.image_eq_preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelIso.image_eq_preimage_symm (e : r ≃r s) (t : Set α) : e '' t = e.symm ⁻
¹' t
参数：e : r ≃r s；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem RelIso.image_eq_preimage_symm (e : r ≃r s) (t : Set α) : e '' t = e.symm ⁻¹' t :=
  e.toEquiv.image_eq_preimage_symm t
/-
**RelIso.preimage_eq_image_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelIso.preimage_eq_image_symm (e : r ≃r s) (t : Set β) : e ⁻¹' t = e.symm 
'' t
参数：e : r ≃r s；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelIso.image_eq_preimage_symm`：RelIso.image_eq_preimage_symm (e : r ≃r s
) (t : Set α) : e '' t = e.symm ⁻¹' t
-/
theorem RelIso.preimage_eq_image_symm (e : r ≃r s) (t : Set β) : e ⁻¹' t = e.symm '' t := by
  rw [e.symm.image_eq_preimage_symm]; rfl

end image

/-
**Acc.of_subrel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Acc.of_subrel {r : α -> α -> Prop} [IsTrans α r] {b : α} (a : { a // r a b
 }) (h : Acc (Subrel r (r · b)) a) : Acc r a.1
参数：a : { a // r a b }；h : Acc (Subrel r (r · b)) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Acc.of_subrel {r : α → α → Prop} [IsTrans α r] {b : α} (a : { a // r a b })
    (h : Acc (Subrel r (r · b)) a) : Acc r a.1 :=
  h.recOn fun a _ IH ↦ ⟨_, fun _ hb ↦ IH ⟨_, _root_.trans hb a.2⟩ hb⟩

/-- A relation `r` is well-founded iff every downward-interval `{ a | r a b }` of it is
well-founded. -/
/-
**wellFounded_iff_wellFounded_subrel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellFounded_iff_wellFounded_subrel {r : α -> α -> Prop} [IsTrans α r] : We
llFounded r ↔ forall b, WellFounded (Subrel r (r · b)) where mp h _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `Acc.of_subrel`：Acc.of_subrel {r : α -> α -> Prop} [IsTrans α r] {b : α} 
(a : { a // r a b }) (h : Acc (Subrel r (r · b)) a) : Acc r a.1
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a

--- 原说明 ---
A relation `r` is well-founded iff every downward-interval `{ a | r a b }` of it
 is
well-founded.
-/
theorem wellFounded_iff_wellFounded_subrel {r : α → α → Prop} [IsTrans α r] :
    WellFounded r ↔ ∀ b, WellFounded (Subrel r (r · b)) where
  mp h _ := InvImage.wf Subtype.val h
  mpr h := ⟨fun a ↦ ⟨_, fun b hr ↦ ((h a).apply _).of_subrel ⟨b, hr⟩⟩⟩
