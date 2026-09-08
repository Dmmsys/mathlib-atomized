/-
Copyright (c) 2024 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.Order.CompleteSublattice

/-!
# `SetLike` instance for elements of `CompleteSublattice (Set X)`

This file provides lemmas for the `SetLike` instance for elements of `CompleteSublattice (Set X)`
-/

public section

attribute [local instance] SetLike.instSubtypeSet

namespace Sublattice

variable {X : Type*} {L : Sublattice (Set X)}

variable {S T : L} {x : X}

/-
**Sublattice.ext_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {X : Type u_1} {L : Sublattice (Set X)} {S T : ↥L}, (∀ (x : X), x ∈ S ↔ 
x ∈ T) → S = T
参数：Set X；∀ (x : X), x ∈ S ↔ x ∈ T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
@[ext] lemma ext_mem (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h
/-
**Sublattice.mem_subtype** 是 Mathlib 中的一个引理，位于命名空间 `Sublattice`。
形式化陈述：mem_subtype : x in L.subtype T ↔ x in T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_subtype : x ∈ L.subtype T ↔ x ∈ T := Iff.rfl
/-
**Sublattice.setLike_mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {X : Type u_1} {L : Sublattice (Set X)} {S T : ↥L} {x : X}, x ∈ S ⊓ T ↔ 
x ∈ S ∧ x ∈ T
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `InfHomClass.map_inf`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Min α} {inst_1 : Min β} {inst_2 : FunLike F α β}   [self : InfHomClass F α β
] (f : F)…
· 使用定理 `LatticeHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `LatticeHom.instLatticeHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Lattice α] [inst_1 : Lattice β], LatticeHomClass (LatticeHom α β) α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma setLike_mem_inf : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := by simp [← mem_subtype]
/-
**Sublattice.setLike_mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {X : Type u_1} {L : Sublattice (Set X)} {S T : ↥L} {x : X}, x ∈ S ⊔ T ↔ 
x ∈ S ∨ x ∈ T
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `LatticeHom.instLatticeHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Lattice α] [inst_1 : Lattice β], LatticeHomClass (LatticeHom α β) α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma setLike_mem_sup : x ∈ S ⊔ T ↔ x ∈ S ∨ x ∈ T := by simp [← mem_subtype]
/-
**Sublattice.setLike_mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `Sublattice`。
形式化陈述：∀ {X : Type u_1} {L : Sublattice (Set X)} {T : ↥L} {x : X}, x ∈ ↑T ↔ x ∈ T
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma setLike_mem_coe : x ∈ T.val ↔ x ∈ T := Iff.rfl

end Sublattice

namespace CompleteSublattice

variable {X : Type*} {L : CompleteSublattice (Set X)}

variable {S T : L} {𝒮 : Set L} {I : Sort*} {f : I → L} {x : X}

/-
**CompleteSublattice.ext** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {X : Type u_1} {L : CompleteSublattice (Set X)} {S T : ↥L}, (∀ (x : X), 
x ∈ S ↔ x ∈ T) → S = T
参数：Set X；∀ (x : X), x ∈ S ↔ x ∈ T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
@[ext] lemma ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h
/-
**CompleteSublattice.mem_subtype** 是 Mathlib 中的一个引理，位于命名空间 `CompleteSublattice`。
形式化陈述：mem_subtype : x in L.subtype T ↔ x in T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_subtype : x ∈ L.subtype T ↔ x ∈ T := Iff.rfl
/-
**CompleteSublattice.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {X : Type u_1} {L : CompleteSublattice (Set X)} {S T : ↥L} {x : X}, x ∈ 
S ⊓ T ↔ x ∈ S ∧ x ∈ T
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `InfHomClass.map_inf`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Min α} {inst_1 : Min β} {inst_2 : FunLike F α β}   [self : InfHomClass F α β
] (f : F)…
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
· 使用定理 `FrameHomClass.toInfTopHomClass`：∀ {F : Type u_8} {α : Type u_9} {β : Typ
e u_10} {inst : CompleteLattice α} {inst_1 : CompleteLattice β}   {inst_2 : FunL
ike F α β} [self : F…
· 使用定理 `CompleteLatticeHomClass.toFrameHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : 
CompleteLattice β] [CompleteL…
· 使用定理 `CompleteLatticeHom.instCompleteLatticeHomClass`：∀ {α : Type u_2} {β : Ty
pe u_3} [inst : CompleteLattice α] [inst_1 : CompleteLattice β],   CompleteLatti
ceHomClass (CompleteLatticeHom α β) …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_inf : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := by simp [← mem_subtype]
/-
**CompleteSublattice.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {X : Type u_1} {L : CompleteSublattice (Set X)} {𝒮 : Set ↥L} {x : X}, x 
∈ sInf 𝒮 ↔ ∀ T ∈ 𝒮, x ∈ T
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sInfHomClass.map_sInf`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {
inst : InfSet α} {inst_1 : InfSet β} {inst_2 : FunLike F α β}   [self : sInfHomC
lass F α β]…
· 使用定理 `CompleteLatticeHomClass.tosInfHomClass`：∀ {F : Type u_8} {α : Type u_9} 
{β : Type u_10} {inst : CompleteLattice α} {inst_1 : CompleteLattice β}   {inst_
2 : FunLike F α β} [self : C…
· 使用定理 `CompleteLatticeHom.instCompleteLatticeHomClass`：∀ {α : Type u_2} {β : Ty
pe u_3} [inst : CompleteLattice α] [inst_1 : CompleteLattice β],   CompleteLatti
ceHomClass (CompleteLatticeHom α β) …
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_sInf : x ∈ sInf 𝒮 ↔ ∀ T ∈ 𝒮, x ∈ T := by simp [← mem_subtype]
/-
**CompleteSublattice.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {X : Type u_1} {L : CompleteSublattice (Set X)} {I : Sort u_2} {f : I → 
↥L} {x : X}, x ∈ ⨅ i, f i ↔ ∀ (i : I), x ∈ f i
参数：Set X；i : I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_iInf`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Sort u_6} 
[inst : FunLike F α β] [inst_1 : InfSet α]   [inst_2 : InfSet β] [sInfHomClass…
· 使用定理 `CompleteLatticeHomClass.tosInfHomClass`：∀ {F : Type u_8} {α : Type u_9} 
{β : Type u_10} {inst : CompleteLattice α} {inst_1 : CompleteLattice β}   {inst_
2 : FunLike F α β} [self : C…
· 使用定理 `CompleteLatticeHom.instCompleteLatticeHomClass`：∀ {α : Type u_2} {β : Ty
pe u_3} [inst : CompleteLattice α] [inst_1 : CompleteLattice β],   CompleteLatti
ceHomClass (CompleteLatticeHom α β) …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_iInf : x ∈ ⨅ i : I, f i ↔ ∀ i : I, x ∈ f i := by simp [← mem_subtype]
/-
**CompleteSublattice.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {X : Type u_1} {L : CompleteSublattice (Set X)} {x : X}, x ∈ ⊤
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopHomClass.map_top`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Top α} {inst_1 : Top β}   {inst_2 : FunLike F α β} [se
lf : TopH…
· 使用定理 `InfTopHomClass.toTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : Min α] [inst_2 : Min β] [inst_3 : Top α]  
 [inst_4 : Top β] …
· 使用定理 `FrameHomClass.toInfTopHomClass`：∀ {F : Type u_8} {α : Type u_9} {β : Typ
e u_10} {inst : CompleteLattice α} {inst_1 : CompleteLattice β}   {inst_2 : FunL
ike F α β} [self : F…
· 使用定理 `CompleteLatticeHomClass.toFrameHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : 
CompleteLattice β] [CompleteL…
· 使用定理 `CompleteLatticeHom.instCompleteLatticeHomClass`：∀ {α : Type u_2} {β : Ty
pe u_3} [inst : CompleteLattice α] [inst_1 : CompleteLattice β],   CompleteLatti
ceHomClass (CompleteLatticeHom α β) …
-/
@[simp] lemma mem_top : x ∈ (⊤ : L) := by simp [← mem_subtype]
/-
**CompleteSublattice.mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {X : Type u_1} {L : CompleteSublattice (Set X)} {S T : ↥L} {x : X}, x ∈ 
S ⊔ T ↔ x ∈ S ∨ x ∈ T
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `sSupHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : CompleteLa
ttice β] [sSupHomCl…
· 使用定理 `CompleteLatticeHomClass.tosSupHomClass`：∀ {F : Type u_8} {α : Type u_9} 
{β : Type u_10} {inst : CompleteLattice α} {inst_1 : CompleteLattice β}   {inst_
2 : FunLike F α β} [self : C…
· 使用定理 `CompleteLatticeHom.instCompleteLatticeHomClass`：∀ {α : Type u_2} {β : Ty
pe u_3} [inst : CompleteLattice α] [inst_1 : CompleteLattice β],   CompleteLatti
ceHomClass (CompleteLatticeHom α β) …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_sup : x ∈ S ⊔ T ↔ x ∈ S ∨ x ∈ T := by simp [← mem_subtype]
/-
**CompleteSublattice.mem_sSup** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {X : Type u_1} {L : CompleteSublattice (Set X)} {𝒮 : Set ↥L} {x : X}, x 
∈ sSup 𝒮 ↔ ∃ T ∈ 𝒮, x ∈ T
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sSupHomClass.map_sSup`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {
inst : SupSet α} {inst_1 : SupSet β} {inst_2 : FunLike F α β}   [self : sSupHomC
lass F α β]…
· 使用定理 `CompleteLatticeHomClass.tosSupHomClass`：∀ {F : Type u_8} {α : Type u_9} 
{β : Type u_10} {inst : CompleteLattice α} {inst_1 : CompleteLattice β}   {inst_
2 : FunLike F α β} [self : C…
· 使用定理 `CompleteLatticeHom.instCompleteLatticeHomClass`：∀ {α : Type u_2} {β : Ty
pe u_3} [inst : CompleteLattice α] [inst_1 : CompleteLattice β],   CompleteLatti
ceHomClass (CompleteLatticeHom α β) …
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_sSup : x ∈ sSup 𝒮 ↔ ∃ T ∈ 𝒮, x ∈ T := by simp [← mem_subtype]
/-
**CompleteSublattice.mem_iSup** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {X : Type u_1} {L : CompleteSublattice (Set X)} {I : Sort u_2} {f : I → 
↥L} {x : X}, x ∈ ⨆ i, f i ↔ ∃ i, x ∈ f i
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_iSup`：map_iSup [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g
 : ι -> α) : f (⨆ i, g i) = ⨆ i, f (g i)
· 使用定理 `CompleteLatticeHomClass.tosSupHomClass`：∀ {F : Type u_8} {α : Type u_9} 
{β : Type u_10} {inst : CompleteLattice α} {inst_1 : CompleteLattice β}   {inst_
2 : FunLike F α β} [self : C…
· 使用定理 `CompleteLatticeHom.instCompleteLatticeHomClass`：∀ {α : Type u_2} {β : Ty
pe u_3} [inst : CompleteLattice α] [inst_1 : CompleteLattice β],   CompleteLatti
ceHomClass (CompleteLatticeHom α β) …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_iSup : x ∈ ⨆ i : I, f i ↔ ∃ i : I, x ∈ f i := by simp [← mem_subtype]
/-
**CompleteSublattice.notMem_bot** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {X : Type u_1} {L : CompleteSublattice (Set X)} {x : X}, x ∉ ⊥
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BotHomClass.map_bot`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Bot α} {inst_1 : Bot β}   {inst_2 : FunLike F α β} [se
lf : BotH…
· 使用定理 `SupBotHomClass.toBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : Max α] [inst_2 : Max β] [inst_3 : Bot α]  
 [inst_4 : Bot β] …
· 使用定理 `sSupHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : CompleteLa
ttice β] [sSupHomCl…
· 使用定理 `CompleteLatticeHomClass.tosSupHomClass`：∀ {F : Type u_8} {α : Type u_9} 
{β : Type u_10} {inst : CompleteLattice α} {inst_1 : CompleteLattice β}   {inst_
2 : FunLike F α β} [self : C…
· 使用定理 `CompleteLatticeHom.instCompleteLatticeHomClass`：∀ {α : Type u_2} {β : Ty
pe u_3} [inst : CompleteLattice α] [inst_1 : CompleteLattice β],   CompleteLatti
ceHomClass (CompleteLatticeHom α β) …
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma notMem_bot : x ∉ (⊥ : L) := by simp [← mem_subtype]

end CompleteSublattice

