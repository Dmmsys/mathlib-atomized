/-
Copyright (c) 2024 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Order.ProjIcc

/-!
# Continuous bundled maps on intervals

In this file we prove a few results about `ContinuousMap` when the domain is an interval.
-/

@[expose] public section

open Set ContinuousMap Filter Topology

namespace ContinuousMap

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
variable {a b c : α} [Fact (a ≤ b)] [Fact (b ≤ c)]
variable {E : Type*} [TopologicalSpace E]

/-- The embedding into an interval from a sub-interval lying on the left, as a `ContinuousMap`. -/
/-
**ContinuousMap.IccInclusionLeft** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：IccInclusionLeft : C(Icc a b, Icc a c)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding into an interval from a sub-interval lying on the left, as a `Cont
inuousMap`.
-/
def IccInclusionLeft : C(Icc a b, Icc a c) :=
  .inclusion <| Icc_subset_Icc le_rfl Fact.out

/-- The embedding into an interval from a sub-interval lying on the right, as a `ContinuousMap`. -/
/-
**ContinuousMap.IccInclusionRight** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：IccInclusionRight : C(Icc b c, Icc a c)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding into an interval from a sub-interval lying on the right, as a `Con
tinuousMap`.
-/
def IccInclusionRight : C(Icc b c, Icc a c) :=
  .inclusion <| Icc_subset_Icc Fact.out le_rfl

/-- The map `projIcc` from `α` onto an interval in `α`, as a `ContinuousMap`. -/
/-
**ContinuousMap.projIccCM** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：projIccCM : C(α, Icc a b)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `projIcc` from `α` onto an interval in `α`, as a `ContinuousMap`.
-/
def projIccCM : C(α, Icc a b) :=
  ⟨projIcc a b Fact.out, continuous_projIcc⟩

/-- The extension operation from continuous maps on an interval to continuous maps on the whole
  type, as a `ContinuousMap`. -/
/-
**ContinuousMap.IccExtendCM** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：IccExtendCM : C(C(Icc a b, E), C(α, E)) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension operation from continuous maps on an interval to continuous maps o
n the whole
  type, as a `ContinuousMap`.
-/
def IccExtendCM : C(C(Icc a b, E), C(α, E)) where
  toFun f := f.comp projIccCM
  continuous_toFun := continuous_precomp projIccCM

@[simp]
/-
**ContinuousMap.IccExtendCM_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：IccExtendCM_of_mem {f : C(Icc a b, E)} {x : α} (hx : x in Icc a b) : IccEx
tendCM f x = f ⟨x, hx⟩
参数：Icc a b, E；hx : x in Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IccExtendCM_of_mem {f : C(Icc a b, E)} {x : α} (hx : x ∈ Icc a b) :
    IccExtendCM f x = f ⟨x, hx⟩ := by
  simp [IccExtendCM, projIccCM, projIcc, hx.1, hx.2]

set_option backward.isDefEq.respectTransparency false in
/-- The concatenation of two continuous maps defined on adjacent intervals. If the values of the
functions on the common bound do not agree, this is defined as an arbitrarily chosen constant
map. See `concatCM` for the corresponding map on the subtype of compatible function pairs. -/
/-
**ContinuousMap.concat** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：concat (f : C(Icc a b, E)) (g : C(Icc b c, E)) : C(Icc a c, E)
参数：f : C(Icc a b, E)；g : C(Icc b c, E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The concatenation of two continuous maps defined on adjacent intervals. If the v
alues of the
functions on the common bound do not agree, this is defined as an arbitrarily ch
osen constant
map. See `concatCM` for the corresponding map on the subtype of compatible funct
ion pairs.
-/
noncomputable def concat (f : C(Icc a b, E)) (g : C(Icc b c, E)) :
    C(Icc a c, E) := by
  by_cases hb : f ⊤ = g ⊥
  · let h (t : α) : E := if t ≤ b then IccExtendCM f t else IccExtendCM g t
    suffices Continuous h from ⟨fun t => h t, by fun_prop⟩
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    rintro x rfl
    simpa [IccExtendCM, projIccCM]
  · exact .const _ (f ⊥) -- junk value

variable {f : C(Icc a b, E)} {g : C(Icc b c, E)}
/-
**ContinuousMap.concat_comp_IccInclusionLeft** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMap`。
形式化陈述：concat_comp_IccInclusionLeft (hb : f ⊤ = g ⊥) : (concat f g).comp IccInclu
sionLeft = f
参数：hb : f ⊤ = g ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `continuous_inclusion`：continuous_inclusion {s t : Set X} (h : s subseteq
 t) : Continuous (inclusion h)
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.projIcc_val`：projIcc_val (x : Icc a b) : projIcc a b h x = x
-/
theorem concat_comp_IccInclusionLeft (hb : f ⊤ = g ⊥) :
    (concat f g).comp IccInclusionLeft = f := by
  ext x
  simp [concat, IccExtendCM, hb, IccInclusionLeft, projIccCM, inclusion, x.2.2]
/-
**ContinuousMap.concat_comp_IccInclusionRight** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousMap`。
形式化陈述：concat_comp_IccInclusionRight (hb : f ⊤ = g ⊥) : (concat f g).comp IccIncl
usionRight = g
参数：hb : f ⊤ = g ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `continuous_inclusion`：continuous_inclusion {s t : Set X} (h : s subseteq
 t) : Continuous (inclusion h)
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Set.projIcc_right`：projIcc_right : projIcc a b h b = ⟨b, right_mem_Icc.2
 h⟩
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
-/
theorem concat_comp_IccInclusionRight (hb : f ⊤ = g ⊥) :
    (concat f g).comp IccInclusionRight = g := by
  ext ⟨x, hx⟩
  obtain rfl | hxb := eq_or_ne x b
  · simpa [concat, IccInclusionRight, IccExtendCM, projIccCM, inclusion, hb]
  · have h : ¬ x ≤ b := lt_of_le_of_ne hx.1 (Ne.symm hxb) |>.not_ge
    simp [concat, hb, IccInclusionRight, h, IccExtendCM, projIccCM, projIcc, inclusion, hx.2, hx.1]

@[simp]
/-
**ContinuousMap.concat_left** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：concat_left (hb : f ⊤ = g ⊥) {t : Icc a c} (ht : t <= b) : concat f g t = 
f ⟨t, t.2.1, ht⟩
参数：hb : f ⊤ = g ⊥；ht : t <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.concat_comp_IccInclusionLeft`：concat_comp_IccInclusionLeft
 (hb : f ⊤ = g ⊥) : (concat f g).comp IccInclusionLeft = f
-/
theorem concat_left (hb : f ⊤ = g ⊥) {t : Icc a c} (ht : t ≤ b) :
    concat f g t = f ⟨t, t.2.1, ht⟩ := by
  nth_rewrite 2 [← concat_comp_IccInclusionLeft hb]
  rfl

@[simp]
/-
**ContinuousMap.concat_right** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：concat_right (hb : f ⊤ = g ⊥) {t : Icc a c} (ht : b <= t) : concat f g t =
 g ⟨t, ht, t.2.2⟩
参数：hb : f ⊤ = g ⊥；ht : b <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.concat_comp_IccInclusionRight`：concat_comp_IccInclusionRig
ht (hb : f ⊤ = g ⊥) : (concat f g).comp IccInclusionRight = g
-/
theorem concat_right (hb : f ⊤ = g ⊥) {t : Icc a c} (ht : b ≤ t) :
    concat f g t = g ⟨t, ht, t.2.2⟩ := by
  nth_rewrite 2 [← concat_comp_IccInclusionRight hb]
  rfl
/-
**ContinuousMap.tendsto_concat** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：tendsto_concat {ι : Type*} {p : Filter ι} {F : ι -> C(Icc a b, E)} {G : ι 
-> C(Icc b c, E)} (hfg : forallᶠ i in p, (F i) ⊤ = (G i) ⊥) (hfg' : f ⊤ = g ⊥) (
hf : Tendsto F p (𝓝 f)) (hg : Tendsto G p (𝓝 g)) : Tendsto (fun i => concat (F i
) (G i)) p (𝓝 (concat f g))
参数：Icc a b, E；Icc b c, E；hfg : forallᶠ i in p, (F i) ⊤ = (G i) ⊥；hfg' : f ⊤ = g 
⊥；hf : Tendsto F p (𝓝 f)；hg : Tendsto G p (𝓝 g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMap.tendsto_nhds_compactOpen`：tendsto_nhds_compactOpen {l : Fi
lter α} {f : α -> C(Y, Z)} {g : C(Y, Z)} : Tendsto f l (𝓝 g) ↔ forall K, IsCompa
ct K -> forall U, IsOpen U -…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Subtype.instOrderClosedTopology`：∀ {α : Type u} [inst : TopologicalSpace
 α] [inst_1 : Preorder α] [t : OrderClosedTopology α] {p : α → Prop},   OrderClo
sedTopology (Subtype …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.concat_comp_IccInclusionLeft`：concat_comp_IccInclusionLeft
 (hb : f ⊤ = g ⊥) : (concat f g).comp IccInclusionLeft = f
· 使用定理 `Set.MapsTo.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set
 α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.MapsTo g t p → Set.Ma
psTo …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `ContinuousMap.concat_comp_IccInclusionRight`：concat_comp_IccInclusionRig
ht (hb : f ⊤ = g ⊥) : (concat f g).comp IccInclusionRight = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContinuousMap.concat_left`：concat_left (hb : f ⊤ = g ⊥) {t : Icc a c} (h
t : t <= b) : concat f g t = f ⟨t, t.2.1, ht⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 32 条，此处仅展示前 30 条）
-/
theorem tendsto_concat {ι : Type*} {p : Filter ι} {F : ι → C(Icc a b, E)} {G : ι → C(Icc b c, E)}
    (hfg : ∀ᶠ i in p, (F i) ⊤ = (G i) ⊥) (hfg' : f ⊤ = g ⊥)
    (hf : Tendsto F p (𝓝 f)) (hg : Tendsto G p (𝓝 g)) :
    Tendsto (fun i => concat (F i) (G i)) p (𝓝 (concat f g)) := by
  rw [tendsto_nhds_compactOpen] at hf hg ⊢
  rintro K hK U hU hfgU
  have h : b ∈ Icc a c := ⟨Fact.out, Fact.out⟩
  let K₁ : Set (Icc a b) := projIccCM '' Subtype.val '' (K ∩ Iic ⟨b, h⟩)
  let K₂ : Set (Icc b c) := projIccCM '' Subtype.val '' (K ∩ Ici ⟨b, h⟩)
  have hK₁ : IsCompact K₁ :=
    hK.inter_right isClosed_Iic |>.image continuous_subtype_val |>.image projIccCM.continuous
  have hK₂ : IsCompact K₂ :=
    hK.inter_right isClosed_Ici |>.image continuous_subtype_val |>.image projIccCM.continuous
  have hfU : MapsTo f K₁ U := by
    rw [← concat_comp_IccInclusionLeft hfg']
    apply hfgU.comp
    rintro x ⟨y, ⟨⟨z, hz⟩, ⟨h1, (h2 : z ≤ b)⟩, rfl⟩, rfl⟩
    simpa [projIccCM, projIcc, h2, hz.1] using! h1
  have hgU : MapsTo g K₂ U := by
    rw [← concat_comp_IccInclusionRight hfg']
    apply hfgU.comp
    rintro x ⟨y, ⟨⟨z, hz⟩, ⟨h1, (h2 : b ≤ z)⟩, rfl⟩, rfl⟩
    simpa [projIccCM, projIcc, h2, hz.2] using! h1
  filter_upwards [hf K₁ hK₁ U hU hfU, hg K₂ hK₂ U hU hgU, hfg] with i hf hg hfg x hx
  by_cases! hxb : x ≤ b
  · rw [concat_left hfg hxb]
    refine hf ⟨x, ⟨x, ⟨hx, hxb⟩, rfl⟩, ?_⟩
    simp [projIccCM, projIcc, hxb, x.2.1]
  · replace hxb : b ≤ x := hxb.le
    rw [concat_right hfg hxb]
    refine hg ⟨x, ⟨x, ⟨hx, hxb⟩, rfl⟩, ?_⟩
    simp [projIccCM, projIcc, hxb, x.2.2]

/-- The concatenation of compatible pairs of continuous maps on adjacent intervals, defined as a
`ContinuousMap` on a subtype of the product. -/
/-
**ContinuousMap.concatCM** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：concatCM : C({fg : C(Icc a b, E) × C(Icc b c, E) // fg.1 ⊤ = fg.2 ⊥}, C(Ic
c a c, E)) where toFun fg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The concatenation of compatible pairs of continuous maps on adjacent intervals, 
defined as a
`ContinuousMap` on a subtype of the product.
-/
noncomputable def concatCM :
    C({fg : C(Icc a b, E) × C(Icc b c, E) // fg.1 ⊤ = fg.2 ⊥}, C(Icc a c, E)) where
  toFun fg := concat fg.val.1 fg.val.2
  continuous_toFun := by
    let S : Set (C(Icc a b, E) × C(Icc b c, E)) := {fg | fg.1 ⊤ = fg.2 ⊥}
    change Continuous (S.domRestrict concat.uncurry)
    refine continuousOn_iff_continuous_domRestrict.mp (fun fg hfg => ?_)
    refine tendsto_concat ?_ hfg ?_ ?_
    · exact eventually_nhdsWithin_of_forall (fun _ => id)
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_fst
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_snd

@[simp]
/-
**ContinuousMap.concatCM_left** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：concatCM_left {x : Icc a c} (hx : x <= b) {fg : {fg : C(Icc a b, E) × C(Ic
c b c, E) // fg.1 ⊤ = fg.2 ⊥}} : concatCM fg x = fg.1.1 ⟨x.1, x.2.1, hx⟩
参数：hx : x <= b；Icc a b, E；Icc b c, E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.concat_left`：concat_left (hb : f ⊤ = g ⊥) {t : Icc a c} (h
t : t <= b) : concat f g t = f ⟨t, t.2.1, ht⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem concatCM_left {x : Icc a c} (hx : x ≤ b)
    {fg : {fg : C(Icc a b, E) × C(Icc b c, E) // fg.1 ⊤ = fg.2 ⊥}} :
    concatCM fg x = fg.1.1 ⟨x.1, x.2.1, hx⟩ := by
  exact concat_left fg.2 hx

@[simp]
/-
**ContinuousMap.concatCM_right** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：concatCM_right {x : Icc a c} (hx : b <= x) {fg : {fg : C(Icc a b, E) × C(I
cc b c, E) // fg.1 ⊤ = fg.2 ⊥}} : concatCM fg x = fg.1.2 ⟨x.1, hx, x.2.2⟩
参数：hx : b <= x；Icc a b, E；Icc b c, E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.concat_right`：concat_right (hb : f ⊤ = g ⊥) {t : Icc a c} 
(ht : b <= t) : concat f g t = g ⟨t, ht, t.2.2⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem concatCM_right {x : Icc a c} (hx : b ≤ x)
    {fg : {fg : C(Icc a b, E) × C(Icc b c, E) // fg.1 ⊤ = fg.2 ⊥}} :
    concatCM fg x = fg.1.2 ⟨x.1, hx, x.2.2⟩ :=
  concat_right fg.2 hx

end ContinuousMap

