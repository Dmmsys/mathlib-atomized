/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finsupp.Single

/-!
# Additive monoid structure on `ι →₀ M`
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Finset

noncomputable section

variable {ι F M N O G H : Type*}

namespace Finsupp
section Zero
variable [Zero M] [Zero N] [Zero O]

/-
**Finsupp.apply_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：apply_single [FunLike F M N] [ZeroHomClass F M N] (e : F) (i : ι) (m : M) 
(b : ι) : e (single i m b) = single i (e m) b
参数：e : F；i : ι；m : M；b : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.apply_single'`：apply_single' [Zero N] [Zero P] (e : N -> P) (he 
: e 0 = 0) (a : α) (n : N) (b : α) : e ((single a n) b) = single a (e n) b
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
-/
lemma apply_single [FunLike F M N] [ZeroHomClass F M N] (e : F) (i : ι) (m : M) (b : ι) :
    e (single i m b) = single i (e m) b := apply_single' e (map_zero e) i m b

/-- Composition with a fixed zero-preserving homomorphism is itself a zero-preserving homomorphism
on functions. -/
@[simps]
/-
**Finsupp.mapRange.zeroHom** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.mapRange`。
形式化陈述：{ι : Type u_1} →   {M : Type u_3} → {N : Type u_4} → [inst : Zero M] → [in
st_1 : Zero N] → ZeroHom M N → ZeroHom (ι →₀ M) (ι →₀ N)
参数：ι →₀ M；ι →₀ N。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_
1 : Zero N] (f : ZeroHom M N), f 0 = 0

--- 原说明 ---
Composition with a fixed zero-preserving homomorphism is itself a zero-preservin
g homomorphism
on functions.
-/
def mapRange.zeroHom (f : ZeroHom M N) : ZeroHom (ι →₀ M) (ι →₀ N) where
  toFun := Finsupp.mapRange f f.map_zero
  map_zero' := mapRange_zero
/-
**Finsupp.mapRange.zeroHom_id** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M], Finsupp.mapRange.zeroHom 
(ZeroHom.id M) = ZeroHom.id (ι →₀ M)
参数：ZeroHom.id M；ι →₀ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_1 : Z
ero N] ⦃f g : ZeroHom M N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZeroHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_
1 : Zero N] (f : ZeroHom M N), f 0 = 0
· 使用定理 `Finsupp.mapRange.zeroHom_apply`：∀ {ι : Type u_1} {M : Type u_3} {N : Typ
e u_4} [inst : Zero M] [inst_1 : Zero N] (f : ZeroHom M N) (g : ι →₀ M),   (Fins
upp.mapRange.zeroHom…
· 使用定理 `Finsupp.mapRange_id`：mapRange_id (g : α ->₀ M) : mapRange id rfl g = g
· 使用定理 `ZeroHom.id_apply`：∀ (M : Type u_10) [inst : Zero M] (x : M), (ZeroHom.id
 M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapRange.zeroHom_id : mapRange.zeroHom (.id M) = .id (ι →₀ M) := by ext; simp
/-
**Finsupp.mapRange.zeroHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} {O : Type u_5} [inst : Zero
 M] [inst_1 : Zero N] [inst_2 : Zero O]   (f : ZeroHom N O) (f₂ : ZeroHom M N), 
  Finsupp.mapRange.zeroHom (f.comp f₂) = (Finsupp.mapRange.zeroHom f).comp (Fins
upp.mapRange.zeroHom f₂)
参数：f : ZeroHom N O；f₂ : ZeroHom M N；f.comp f₂；Finsupp.mapRange.zeroHom f；Finsupp
.mapRange.zeroHom f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_1 : Z
ero N] ⦃f g : ZeroHom M N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZeroHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_
1 : Zero N] (f : ZeroHom M N), f 0 = 0
· 使用定理 `Finsupp.mapRange.zeroHom_apply`：∀ {ι : Type u_1} {M : Type u_3} {N : Typ
e u_4} [inst : Zero M] [inst_1 : Zero N] (f : ZeroHom M N) (g : ι →₀ M),   (Fins
upp.mapRange.zeroHom…
· 使用引理 `Finsupp.mapRange_mapRange`：mapRange_mapRange (e₁ : N -> O) (e₂ : M -> N)
 (he₁ he₂) (f : α ->₀ M) : mapRange e₁ he₁ (mapRange e₂ he₂ f) = mapRange (e₁ ∘ 
e₂) (by simp [*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRange.zeroHom_comp (f : ZeroHom N O) (f₂ : ZeroHom M N) :
    mapRange.zeroHom (ι := ι) (f.comp f₂) = (mapRange.zeroHom f).comp (mapRange.zeroHom f₂) := by
  ext; simp

end Zero

section AddZeroClass
variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

/-
**Finsupp.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instAdd : Add (ι ->₀ M) where add
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add (ι →₀ M) where add := zipWith (· + ·) (add_zero 0)
/-
**Finsupp.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass M] (f g : ι →₀ M), ⇑(
f + g) = ⇑f + ⇑g
参数：f g : ι →₀ M；f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_add (f g : ι →₀ M) : ⇑(f + g) = f + g := rfl
/-
**Finsupp.add_apply** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：add_apply (g₁ g₂ : ι ->₀ M) (a : ι) : (g₁ + g₂) a = g₁ a + g₂ a
参数：g₁ g₂ : ι ->₀ M；a : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_apply (g₁ g₂ : ι →₀ M) (a : ι) : (g₁ + g₂) a = g₁ a + g₂ a := rfl
/-
**Finsupp.support_add** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_add [DecidableEq ι] : (g₁ + g₂).support subseteq g₁.support union 
g₂.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_zipWith`：support_zipWith [D : DecidableEq α] {f : M -> N
 -> O} {hf : f 0 0 = 0} {g₁ : α ->₀ M} {g₂ : α ->₀ N} : (zipWith f hf g₁ g₂).sup
port subseteq…
-/
lemma support_add [DecidableEq ι] : (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support := support_zipWith

/-- The support of a sum is the union of the supports when the supports are disjoint.

In the case where the coefficients satisfy `CanonicallyOrderedAdd`, there is also
`Finsupp.support_add_eq_union`, which holds without any disjointness assumption. -/
/-
**Finsupp.support_add_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_add_eq [DecidableEq ι] (h : Disjoint g₁.support g₂.support) : (g₁ 
+ g₂).support = g₁.support union g₂.support
参数：h : Disjoint g₁.support g₂.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finsupp.support_zipWith`：support_zipWith [D : DecidableEq α] {f : M -> N
 -> O} {hf : f 0 0 = 0} {g₁ : α ->₀ M} {g₂ : α ->₀ N} : (zipWith f hf g₁ g₂).sup
port subseteq…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_union_of_disjoint`：mem_union_of_disjoint [DecidableEq α] {s t
 : Finset α} (h : Disjoint s t) {x : α} : x in s union t ↔ Xor (x in s) (x in t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
The support of a sum is the union of the supports when the supports are disjoint
.

In the case where the coefficients satisfy `CanonicallyOrderedAdd`, there is als
o
`Finsupp.support_add_eq_union`, which holds without any disjointness assumption.
-/
lemma support_add_eq [DecidableEq ι] (h : Disjoint g₁.support g₂.support) :
    (g₁ + g₂).support = g₁.support ∪ g₂.support :=
  le_antisymm support_zipWith fun a ha => by
    cases (Finset.mem_union_of_disjoint h).mp ha <;> simp_all
/-
**Finsupp.instAddZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instAddZeroClass : AddZeroClass (ι ->₀ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddZeroClass : AddZeroClass (ι →₀ M) :=
  fast_instance% DFunLike.coe_injective.addZeroClass _ coe_zero coe_add
/-
**Finsupp.instIsLeftCancelAdd** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instIsLeftCancelAdd [IsLeftCancelAdd M] : IsLeftCancelAdd (ι ->₀ M) where 
add_left_cancel _ _ _ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
instance instIsLeftCancelAdd [IsLeftCancelAdd M] : IsLeftCancelAdd (ι →₀ M) where
  add_left_cancel _ _ _ h := ext fun x => add_left_cancel <| DFunLike.congr_fun h x

/-- When ι is finite and M is an AddMonoid,
  then Finsupp.equivFunOnFinite gives an AddEquiv -/
/-
**Finsupp.addEquivFunOnFinite** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：addEquivFunOnFinite {ι : Type*} [Finite ι] : (ι ->₀ M) ≃+ (ι -> M) where _
_
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When ι is finite and M is an AddMonoid,
  then Finsupp.equivFunOnFinite gives an AddEquiv
-/
noncomputable def addEquivFunOnFinite {ι : Type*} [Finite ι] :
    (ι →₀ M) ≃+ (ι → M) where
  __ := Finsupp.equivFunOnFinite
  map_add' _ _ := rfl

/-- If `M` is the trivial monoid, then the monoid of finitely supported functions `ι →₀ M` is
is isomorphic to `M`. -/
@[simps! apply symm_apply]
/-
**Finsupp.uniqueAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：uniqueAddEquiv (i : ι) [Subsingleton ι] : (ι ->₀ M) ≃+ M where toEquiv
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is the trivial monoid, then the monoid of finitely supported functions `ι
 →₀ M` is
is isomorphic to `M`.
-/
noncomputable def uniqueAddEquiv (i : ι) [Subsingleton ι] : (ι →₀ M) ≃+ M where
  toEquiv := uniqueEquiv i
  map_add' _ _ := rfl

-- We want this lemma to fire before `uniqueAddEquiv_symm_apply`.
/-
**Finsupp.uniqueAddEquiv_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass M] (i : ι) [inst_1 : 
Subsingleton ι] (m : M) (j : ι),   ((Finsupp.uniqueAddEquiv i).symm m) j = m
参数：i : ι；m : M；j : ι；(Finsupp.uniqueAddEquiv i).symm m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.uniqueAddEquiv_symm_apply`：∀ {ι : Type u_1} {M : Type u_3} [inst
 : AddZeroClass M] (i : ι) [inst_1 : Subsingleton ι] (b : M),   (Finsupp.uniqueA
ddEquiv i).symm b = fun…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp↓ high] lemma uniqueAddEquiv_symm_apply_apply (i : ι) [Subsingleton ι] (m : M) (j : ι) :
    (uniqueAddEquiv i).symm m j = m := by simp [Subsingleton.elim j i]

/-- If `M` is the trivial monoid, then the monoid of finitely supported functions `ι →₀ M` is
is isomorphic to `M`. -/
@[simps!, deprecated uniqueAddEquiv (since := "2026-05-06")]
/-
**Finsupp._root_.AddEquiv.finsuppUnique** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is the trivial monoid, then the monoid of finitely supported functions `ι
 →₀ M` is
is isomorphic to `M`.
-/
noncomputable def _root_.AddEquiv.finsuppUnique {ι : Type*} [Unique ι] : (ι →₀ M) ≃+ M where
  toEquiv := .finsuppUnique
  map_add' _ _ := rfl
/-
**Finsupp.instIsRightCancelAdd** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instIsRightCancelAdd [IsRightCancelAdd M] : IsRightCancelAdd (ι ->₀ M) whe
re add_right_cancel _ _ _ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
instance instIsRightCancelAdd [IsRightCancelAdd M] : IsRightCancelAdd (ι →₀ M) where
  add_right_cancel _ _ _ h := ext fun x => add_right_cancel <| DFunLike.congr_fun h x
/-
**Finsupp.instIsCancelAdd** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass M] [IsCancelAdd M], I
sCancelAdd (ι →₀ M)
参数：ι →₀ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsCancelAdd.toIsRightCancelAdd`：∀ {G : Type u} {inst : Add G} [self : Is
CancelAdd G], IsRightCancelAdd G
-/
instance instIsCancelAdd [IsCancelAdd M] : IsCancelAdd (ι →₀ M) where

/-- Evaluation of a function `f : ι →₀ M` at a point as an additive monoid homomorphism.

See `Finsupp.lapply` in `Mathlib/LinearAlgebra/Finsupp/Defs.lean` for the stronger version as a
linear map. -/
@[simps apply]
/-
**Finsupp.applyAddHom** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：applyAddHom (a : ι) : (ι ->₀ M) ->+ M where toFun g
参数：a : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.add_apply`：add_apply (g₁ g₂ : ι ->₀ M) (a : ι) : (g₁ + g₂) a = g
₁ a + g₂ a

--- 原说明 ---
Evaluation of a function `f : ι →₀ M` at a point as an additive monoid homomorph
ism.

See `Finsupp.lapply` in `Mathlib/LinearAlgebra/Finsupp/Defs.lean` for the strong
er version as a
linear map.
-/
def applyAddHom (a : ι) : (ι →₀ M) →+ M where
  toFun g := g a
  map_zero' := zero_apply
  map_add' _ _ := add_apply _ _ _

/-- Coercion from a `Finsupp` to a function type is an `AddMonoidHom`. -/
@[simps]
/-
**Finsupp.coeFnAddHom** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：coeFnAddHom : (ι ->₀ M) ->+ ι -> M where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.coe_add`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass M]
 (f g : ι →₀ M), ⇑(f + g) = ⇑f + ⇑g

--- 原说明 ---
Coercion from a `Finsupp` to a function type is an `AddMonoidHom`.
-/
noncomputable def coeFnAddHom : (ι →₀ M) →+ ι → M where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
/-
**Finsupp.mapRange_add** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_add {hf : f 0 = 0} (hf' : forall x y, f (x + y) = f x + f y) (v₁ 
v₂ : ι ->₀ M) : mapRange f hf (v₁ + v₂) = mapRange f hf v₁ + mapRange f hf v₂
参数：hf' : forall x y, f (x + y) = f x + f y；v₁ v₂ : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRange_add {hf : f 0 = 0} (hf' : ∀ x y, f (x + y) = f x + f y) (v₁ v₂ : ι →₀ M) :
    mapRange f hf (v₁ + v₂) = mapRange f hf v₁ + mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', add_apply, mapRange_apply]
/-
**Finsupp.mapRange_add'** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_add' [FunLike F M N] [AddMonoidHomClass F M N] {f : F} (g₁ g₂ : ι
 ->₀ M) : mapRange f (map_zero f) (g₁ + g₂) = mapRange f (map_zero f) g₁ + mapRa
nge f (map_zero f) g₂
参数：g₁ g₂ : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.mapRange_add`：mapRange_add {hf : f 0 = 0} (hf' : forall x y, f (
x + y) = f x + f y) (v₁ v₂ : ι ->₀ M) : mapRange f hf (v₁ + v₂) = mapRange f hf 
v₁ + mapRa…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
-/
lemma mapRange_add' [FunLike F M N] [AddMonoidHomClass F M N] {f : F} (g₁ g₂ : ι →₀ M) :
    mapRange f (map_zero f) (g₁ + g₂) = mapRange f (map_zero f) g₁ + mapRange f (map_zero f) g₂ :=
  mapRange_add (map_add f) g₁ g₂

/-- Bundle `Finsupp.embDomain f` as an additive map from `ι →₀ M` to `F →₀ M`. -/
@[simps]
/-
**Finsupp.embDomain.addMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.embDomain`。
形式化陈述：{ι : Type u_1} → {F : Type u_2} → {M : Type u_3} → [inst : AddZeroClass M]
 → (ι ↪ F) → (ι →₀ M) →+ F →₀ M
参数：ι ↪ F；ι →₀ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle `Finsupp.embDomain f` as an additive map from `ι →₀ M` to `F →₀ M`.
-/
def embDomain.addMonoidHom (f : ι ↪ F) : (ι →₀ M) →+ F →₀ M where
  toFun v := embDomain f v
  map_zero' := by simp
  map_add' v w := by
    ext b
    by_cases h : b ∈ Set.range f
    · rcases h with ⟨a, rfl⟩
      simp
    · simp only [coe_add, Pi.add_apply, embDomain_of_notMem_range _ _ _ h, add_zero]

@[simp]
/-
**Finsupp.embDomain_add** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_add (f : ι ↪ F) (v w : ι ->₀ M) : embDomain f (v + w) = embDomai
n f v + embDomain f w
参数：f : ι ↪ F；v w : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
-/
lemma embDomain_add (f : ι ↪ F) (v w : ι →₀ M) :
    embDomain f (v + w) = embDomain f v + embDomain f w := (embDomain.addMonoidHom f).map_add v w

@[simp]
/-
**Finsupp.single_add** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) = single a b₁ + single
 a b₂
参数：a : ι；b₁ b₂ : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.zipWith_single_single`：zipWith_single_single (f : M -> N -> P) (
hf : f 0 0 = 0) (a : α) (m : M) (n : N) : zipWith f hf (single a m) (single a n)
 = single a (f m n)
-/
lemma single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
  (zipWith_single_single _ _ _ _ _).symm
/-
**Finsupp.single_add_apply** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：single_add_apply (a : ι) (m₁ m₂ : M) (b : ι) : single a (m₁ + m₂) b = sing
le a m₁ b + single a m₂ b
参数：a : ι；m₁ m₂ : M；b : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma single_add_apply (a : ι) (m₁ m₂ : M) (b : ι) :
    single a (m₁ + m₂) b = single a m₁ b + single a m₂ b := by simp
/-
**Finsupp.support_single_add** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_single_add {a : ι} {b : M} {f : ι ->₀ M} (ha : a ∉ f.support) (hb 
: b != 0) : support (single a b + f) = cons a f.support ha
参数：ha : a ∉ f.support；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.support_add_eq`：support_add_eq [DecidableEq ι] (h : Disjoint g₁.
support g₂.support) : (g₁ + g₂).support = g₁.support union g₂.support
· 使用定理 `Finset.disjoint_singleton_left`：disjoint_singleton_left : Disjoint (sing
leton a) s ↔ a ∉ s
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.insert_eq`：insert_eq (a : α) (s : Finset α) : insert a s = {a} un
ion s
-/
lemma support_single_add {a : ι} {b : M} {f : ι →₀ M} (ha : a ∉ f.support) (hb : b ≠ 0) :
    support (single a b + f) = cons a f.support ha := by
  classical
  have H := support_single a hb
  rw [support_add_eq, H, cons_eq_insert, insert_eq]
  rwa [H, disjoint_singleton_left]
/-
**Finsupp.support_add_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_add_single {a : ι} {b : M} {f : ι ->₀ M} (ha : a ∉ f.support) (hb 
: b != 0) : support (f + single a b) = cons a f.support ha
参数：ha : a ∉ f.support；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.support_add_eq`：support_add_eq [DecidableEq ι] (h : Disjoint g₁.
support g₂.support) : (g₁ + g₂).support = g₁.support union g₂.support
· 使用定理 `Finset.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s (
singleton a) ↔ a ∉ s
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.insert_eq`：insert_eq (a : α) (s : Finset α) : insert a s = {a} un
ion s
-/
lemma support_add_single {a : ι} {b : M} {f : ι →₀ M} (ha : a ∉ f.support) (hb : b ≠ 0) :
    support (f + single a b) = cons a f.support ha := by
  classical
  have H := support_single a hb
  rw [support_add_eq, H, union_comm, cons_eq_insert, insert_eq]
  rwa [H, disjoint_singleton_right]
/-
**Finsupp.support_single_add_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_single_add_single [DecidableEq ι] {f₁ f₂ : ι} {g₁ g₂ : M} (H : f₁ 
!= f₂) (hg₁ : g₁ != 0) (hg₂ : g₂ != 0) : (single f₁ g₁ + single f₂ g₂).support =
 {f₁, f₂}
参数：H : f₁ != f₂；hg₁ : g₁ != 0；hg₂ : g₂ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.support_add_eq`：support_add_eq [DecidableEq ι] (h : Disjoint g₁.
support g₂.support) : (g₁ + g₂).support = g₁.support union g₂.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma support_single_add_single [DecidableEq ι] {f₁ f₂ : ι} {g₁ g₂ : M}
    (H : f₁ ≠ f₂) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) :
    (single f₁ g₁ + single f₂ g₂).support = {f₁, f₂} := by
  rw [support_add_eq, support_single _ hg₁, support_single _ hg₂]
  · simp
  · simp [support_single, *]
/-
**Finsupp.support_single_add_single_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_single_add_single_subset [DecidableEq ι] {f₁ f₂ : ι} {g₁ g₂ : M} :
 (single f₁ g₁ + single f₂ g₂).support subseteq {f₁, f₂}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用引理 `Finsupp.support_add`：support_add [DecidableEq ι] : (g₁ + g₂).support sub
seteq g₁.support union g₂.support
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.union_subset_iff`：union_subset_iff : s union t subseteq u ↔ s sub
seteq u ∧ t subseteq u
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma support_single_add_single_subset [DecidableEq ι] {f₁ f₂ : ι} {g₁ g₂ : M} :
    (single f₁ g₁ + single f₂ g₂).support ⊆ {f₁, f₂} := by
  refine subset_trans Finsupp.support_add <| union_subset_iff.mpr ⟨?_, ?_⟩ <;>
  exact subset_trans Finsupp.support_single_subset (by simp)

set_option backward.isDefEq.respectTransparency false in
@[deprecated uniqueAddEquiv_symm_apply (since := "2026-05-06")]
/-
**Finsupp._root_.AddEquiv.finsuppUnique_symm** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AddEquiv.finsuppUnique_symm {M : Type*} [AddZeroClass M] (d : M) :
    AddEquiv.finsuppUnique.symm d = single () d := by ext; simp [AddEquiv.finsuppUnique]
/-
**Finsupp.addCommute_iff_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：addCommute_iff_inter [DecidableEq ι] {f g : ι ->₀ M} : AddCommute f g ↔ fo
rall x in f.support inter g.support, AddCommute (f x) (g x) where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.ext_iff`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M] {f g : 
α →₀ M}, f = g ↔ ∀ (a : α), f a = g a
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Finset.mem_inter_of_mem`：mem_inter_of_mem {a : α} {s₁ s₂ : Finset α} : a
 in s₁ -> a in s₂ -> a in s₁ inter s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem addCommute_iff_inter [DecidableEq ι] {f g : ι →₀ M} :
    AddCommute f g ↔ ∀ x ∈ f.support ∩ g.support, AddCommute (f x) (g x) where
  mp h := fun x _ ↦ Finsupp.ext_iff.1 h x
  mpr h := by
    ext x
    by_cases hf : x ∈ f.support
    · by_cases hg : x ∈ g.support
      · exact h _ (mem_inter_of_mem hf hg)
      · simp_all
    · simp_all
/-
**Finsupp.addCommute_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：addCommute_of_disjoint {f g : ι ->₀ M} (h : Disjoint f.support g.support) 
: AddCommute f g
参数：h : Disjoint f.support g.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem addCommute_of_disjoint {f g : ι →₀ M} (h : Disjoint f.support g.support) :
    AddCommute f g := by
  classical simp_all [addCommute_iff_inter, Finset.disjoint_iff_inter_eq_empty]

/-- `Finsupp.single` as an `AddMonoidHom`.

See `Finsupp.lsingle` in `Mathlib/LinearAlgebra/Finsupp/Defs.lean` for the stronger version as a
linear map. -/
@[simps]
/-
**Finsupp.singleAddHom** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：singleAddHom (a : ι) : M ->+ ι ->₀ M where toFun
参数：a : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂

--- 原说明 ---
`Finsupp.single` as an `AddMonoidHom`.

See `Finsupp.lsingle` in `Mathlib/LinearAlgebra/Finsupp/Defs.lean` for the stron
ger version as a
linear map.
-/
def singleAddHom (a : ι) : M →+ ι →₀ M where
  toFun := single a
  map_zero' := single_zero a
  map_add' := single_add a
/-
**Finsupp.update_eq_single_add_erase** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：update_eq_single_add_erase (f : ι ->₀ M) (a : ι) (b : M) : f.update a b = 
single a b + f.erase a
参数：f : ι ->₀ M；a : ι；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Finsupp.erase_same`：erase_same {a : α} {f : α ->₀ M} : (f.erase a) a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `Finsupp.erase_ne`：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.e
rase a) a' = f a'
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma update_eq_single_add_erase (f : ι →₀ M) (a : ι) (b : M) :
    f.update a b = single a b + f.erase a := by
  classical
    ext j
    rcases eq_or_ne j a with (rfl | h)
    · simp
    · simp [h, erase_ne]
/-
**Finsupp.update_eq_erase_add_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：update_eq_erase_add_single (f : ι ->₀ M) (a : ι) (b : M) : f.update a b = 
f.erase a + single a b
参数：f : ι ->₀ M；a : ι；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Finsupp.erase_same`：erase_same {a : α} {f : α ->₀ M} : (f.erase a) a = 0
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.erase_ne`：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.e
rase a) a' = f a'
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma update_eq_erase_add_single (f : ι →₀ M) (a : ι) (b : M) :
    f.update a b = f.erase a + single a b := by
  classical
    ext j
    rcases eq_or_ne j a with (rfl | h)
    · simp
    · simp [h, erase_ne]
/-
**Finsupp.update_eq_single_add** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：update_eq_single_add {f : ι ->₀ M} {a : ι} (h : f a = 0) (b : M) : f.updat
e a b = single a b + f
参数：h : f a = 0；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.update_eq_single_add_erase`：update_eq_single_add_erase (f : ι ->
₀ M) (a : ι) (b : M) : f.update a b = single a b + f.erase a
· 使用定理 `Finsupp.erase_of_notMem_support`：erase_of_notMem_support {f : α ->₀ M} {
a} (haf : a ∉ f.support) : erase a f = f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma update_eq_single_add {f : ι →₀ M} {a : ι} (h : f a = 0) (b : M) :
    f.update a b = single a b + f := by
  rw [update_eq_single_add_erase, erase_of_notMem_support (by simpa)]
/-
**Finsupp.update_eq_add_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：update_eq_add_single {f : ι ->₀ M} {a : ι} (h : f a = 0) (b : M) : f.updat
e a b = f + single a b
参数：h : f a = 0；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.update_eq_erase_add_single`：update_eq_erase_add_single (f : ι ->
₀ M) (a : ι) (b : M) : f.update a b = f.erase a + single a b
· 使用定理 `Finsupp.erase_of_notMem_support`：erase_of_notMem_support {f : α ->₀ M} {
a} (haf : a ∉ f.support) : erase a f = f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma update_eq_add_single {f : ι →₀ M} {a : ι} (h : f a = 0) (b : M) :
    f.update a b = f + single a b := by
  rw [update_eq_erase_add_single, erase_of_notMem_support (by simpa)]
/-
**Finsupp.single_add_erase** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：single_add_erase (a : ι) (f : ι ->₀ M) : single a (f a) + f.erase a = f
参数：a : ι；f : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.update_eq_single_add_erase`：update_eq_single_add_erase (f : ι ->
₀ M) (a : ι) (b : M) : f.update a b = single a b + f.erase a
· 使用定理 `Finsupp.update_self`：update_self : f.update a (f a) = f
-/
lemma single_add_erase (a : ι) (f : ι →₀ M) : single a (f a) + f.erase a = f := by
  rw [← update_eq_single_add_erase, update_self]
/-
**Finsupp.erase_add_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：erase_add_single (a : ι) (f : ι ->₀ M) : f.erase a + single a (f a) = f
参数：a : ι；f : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.update_eq_erase_add_single`：update_eq_erase_add_single (f : ι ->
₀ M) (a : ι) (b : M) : f.update a b = f.erase a + single a b
· 使用定理 `Finsupp.update_self`：update_self : f.update a (f a) = f
-/
lemma erase_add_single (a : ι) (f : ι →₀ M) : f.erase a + single a (f a) = f := by
  rw [← update_eq_erase_add_single, update_self]

@[simp]
/-
**Finsupp.erase_add** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：erase_add (a : ι) (f f' : ι ->₀ M) : erase a (f + f') = erase a f + erase 
a f'
参数：a : ι；f f' : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.add_apply`：add_apply (g₁ g₂ : ι ->₀ M) (a : ι) : (g₁ + g₂) a = g
₁ a + g₂ a
· 使用定理 `Finsupp.erase_same`：erase_same {a : α} {f : α ->₀ M} : (f.erase a) a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finsupp.erase_ne`：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.e
rase a) a' = f a'
-/
lemma erase_add (a : ι) (f f' : ι →₀ M) : erase a (f + f') = erase a f + erase a f' := by
  ext s; by_cases hs : s = a
  · rw [hs, add_apply, erase_same, erase_same, erase_same, add_zero]
  rw [add_apply, erase_ne hs, erase_ne hs, erase_ne hs, add_apply]

/-- `Finsupp.erase` as an `AddMonoidHom`. -/
@[simps]
/-
**Finsupp.eraseAddHom** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：eraseAddHom (a : ι) : (ι ->₀ M) ->+ ι ->₀ M where toFun
参数：a : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.erase_add`：erase_add (a : ι) (f f' : ι ->₀ M) : erase a (f + f')
 = erase a f + erase a f'

--- 原说明 ---
`Finsupp.erase` as an `AddMonoidHom`.
-/
def eraseAddHom (a : ι) : (ι →₀ M) →+ ι →₀ M where
  toFun := erase a
  map_zero' := erase_zero a
  map_add' := erase_add a

@[elab_as_elim]
/-
**Finsupp.induction** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass M] {motive : (ι →₀ M)
 → Prop} (f : ι →₀ M),   motive 0 →     (∀ (a : ι) (b : M) (f : ι →₀ M), a ∉ f.s
upport → b ≠ 0 → motive f → motive ((fun₀ | a => b) + f)) → motive f
参数：ι →₀ M；f : ι →₀ M；∀ (a : ι) (b : M) (f : ι →₀ M), a ∉ f.support → b ≠ 0 → mot
ive f → motive ((fun₀ | a => b) + f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.support_eq_empty`：support_eq_empty {f : α ->₀ M} : f.support = ∅
 ↔ f = 0
· 使用定理 `Finsupp.support_erase`：support_erase [DecidableEq α] {a : α} {f : α ->₀ 
M} : (f.erase a).support = f.support.erase a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Finset.mem_cons_self`：mem_cons_self (a : α) (s : Finset α) {h} : a in co
ns a s h
· 使用定理 `Finset.erase_cons`：erase_cons {s : Finset α} {a : α} (h : a ∉ s) : (s.co
ns a h).erase a = s
· 使用引理 `Finsupp.single_add_erase`：single_add_erase (a : ι) (f : ι ->₀ M) : singl
e a (f a) + f.erase a = f
-/
protected lemma induction {motive : (ι →₀ M) → Prop} (f : ι →₀ M) (zero : motive 0)
    (single_add : ∀ (a b) (f : ι →₀ M),
      a ∉ f.support → b ≠ 0 → motive f → motive (single a b + f)) : motive f :=
  suffices ∀ (s) (f : ι →₀ M), f.support = s → motive f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
    suffices motive (single a (f a) + f.erase a) by rwa [single_add_erase] at this
    classical
      apply single_add
      · rw [support_erase, mem_erase]
        exact fun H => H.1 rfl
      · rw [← mem_support_iff, hf]
        exact mem_cons_self _ _
      · apply ih _ _
        rw [support_erase, hf, Finset.erase_cons]

@[elab_as_elim]
/-
**Finsupp.induction** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass M] {motive : (ι →₀ M)
 → Prop} (f : ι →₀ M),   motive 0 →     (∀ (a : ι) (b : M) (f : ι →₀ M), a ∉ f.s
upport → b ≠ 0 → motive f → motive ((fun₀ | a => b) + f)) → motive f
参数：ι →₀ M；f : ι →₀ M；∀ (a : ι) (b : M) (f : ι →₀ M), a ∉ f.support → b ≠ 0 → mot
ive f → motive ((fun₀ | a => b) + f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.support_eq_empty`：support_eq_empty {f : α ->₀ M} : f.support = ∅
 ↔ f = 0
· 使用定理 `Finsupp.support_erase`：support_erase [DecidableEq α] {a : α} {f : α ->₀ 
M} : (f.erase a).support = f.support.erase a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Finset.mem_cons_self`：mem_cons_self (a : α) (s : Finset α) {h} : a in co
ns a s h
· 使用定理 `Finset.erase_cons`：erase_cons {s : Finset α} {a : α} (h : a ∉ s) : (s.co
ns a h).erase a = s
· 使用引理 `Finsupp.single_add_erase`：single_add_erase (a : ι) (f : ι ->₀ M) : singl
e a (f a) + f.erase a = f
-/
lemma induction₂ {motive : (ι →₀ M) → Prop} (f : ι →₀ M) (zero : motive 0)
    (add_single : ∀ (a b) (f : ι →₀ M),
      a ∉ f.support → b ≠ 0 → motive f → motive (f + single a b)) : motive f := by
  refine f.induction zero ?_
  convert! add_single using 7
  apply (addCommute_of_disjoint _).eq
  simp_all

@[elab_as_elim]
/-
**Finsupp.induction_linear** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：induction_linear {motive : (ι ->₀ M) -> Prop} (f : ι ->₀ M) (zero : motive
 0) (add : forall f g : ι ->₀ M, motive f -> motive g -> motive (f + g)) (single
 : forall a b, motive (single a b)) : motive f
参数：ι ->₀ M；f : ι ->₀ M；zero : motive 0；add : forall f g : ι ->₀ M, motive f -> m
otive g -> motive (f + g)；single : forall a b, motive (single a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.induction₂`：induction₂ {motive : (ι ->₀ M) -> Prop} (f : ι ->₀ M
) (zero : motive 0) (add_single : forall (a b) (f : ι ->₀ M), a ∉ f.support -> b
 != 0 ->…
-/
lemma induction_linear {motive : (ι →₀ M) → Prop} (f : ι →₀ M) (zero : motive 0)
    (add : ∀ f g : ι →₀ M, motive f → motive g → motive (f + g))
    (single : ∀ a b, motive (single a b)) : motive f :=
  induction₂ f zero fun _a _b _f _ _ w => add _ _ w (single _ _)

section LinearOrder

variable [LinearOrder ι] {motive : (ι →₀ M) → Prop}

/-- A finitely supported function can be built by adding up `single a b` for increasing `a`.

The lemma `induction_on_max₂` swaps the argument order in the sum. -/
/-
**Finsupp.induction_on_max** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：induction_on_max (f : ι ->₀ M) (zero : motive 0) (single_add : forall a b 
(f : ι ->₀ M), (forall c in f.support, c < a) -> b != 0 -> motive f -> motive (s
ingle a b + f)) : motive f
参数：f : ι ->₀ M；zero : motive 0；single_add : forall a b (f : ι ->₀ M), (forall c 
in f.support, c < a) -> b != 0 -> motive f -> motive (single a b + f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on_max`：induction_on_max [DecidableEq α] {motive : Fins
et α -> Prop} (s : Finset α) (empty : motive ∅) (insert : forall a s, (forall x 
in s, x < a) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.support_eq_empty`：support_eq_empty {f : α ->₀ M} : f.support = ∅
 ↔ f = 0
· 使用定理 `Finsupp.support_erase`：support_erase [DecidableEq α] {a : α} {f : α ->₀ 
M} : (f.erase a).support = f.support.erase a
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.single_add_erase`：single_add_erase (a : ι) (f : ι ->₀ M) : singl
e a (f a) + f.erase a = f
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s

--- 原说明 ---
A finitely supported function can be built by adding up `single a b` for increas
ing `a`.

The lemma `induction_on_max₂` swaps the argument order in the sum.
-/
lemma induction_on_max (f : ι →₀ M) (zero : motive 0)
    (single_add : ∀ a b (f : ι →₀ M), (∀ c ∈ f.support, c < a) → b ≠ 0 →
      motive f → motive (single a b + f)) : motive f := by
  suffices ∀ (s) (f : ι →₀ M), f.support = s → motive f from this _ _ rfl
  refine fun s => s.induction_on_max (fun f h => ?_) (fun a s hm hf f hs => ?_)
  · rwa [support_eq_empty.1 h]
  · have hs' : (erase a f).support = s := by
      rw [support_erase, hs, erase_insert (fun ha => (hm a ha).false)]
    rw [← single_add_erase a f]
    refine single_add _ _ _ (fun c hc => hm _ <| hs'.symm ▸ hc) ?_ (hf _ hs')
    rw [← mem_support_iff, hs]
    exact mem_insert_self a s

/-- A finitely supported function can be built by adding up `single a b` for decreasing `a`.

The lemma `induction_on_min₂` swaps the argument order in the sum. -/
/-
**Finsupp.induction_on_min** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：induction_on_min (f : ι ->₀ M) (zero : motive 0) (single_add : forall a b 
(f : ι ->₀ M), (forall c in f.support, a < c) -> b != 0 -> motive f -> motive (s
ingle a b + f)) : motive f
参数：f : ι ->₀ M；zero : motive 0；single_add : forall a b (f : ι ->₀ M), (forall c 
in f.support, a < c) -> b != 0 -> motive f -> motive (single a b + f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.induction_on_max`：induction_on_max (f : ι ->₀ M) (zero : motive 
0) (single_add : forall a b (f : ι ->₀ M), (forall c in f.support, c < a) -> b !
= 0 -> motive …

--- 原说明 ---
A finitely supported function can be built by adding up `single a b` for decreas
ing `a`.

The lemma `induction_on_min₂` swaps the argument order in the sum.
-/
lemma induction_on_min (f : ι →₀ M) (zero : motive 0)
    (single_add : ∀ a b (f : ι →₀ M), (∀ c ∈ f.support, a < c) → b ≠ 0 →
      motive f → motive (single a b + f)) : motive f :=
  induction_on_max (ι := ιᵒᵈ) f zero single_add

/-- A finitely supported function can be built by adding up `single a b` for increasing `a`.

The lemma `induction_on_max` swaps the argument order in the sum. -/
/-
**Finsupp.induction_on_max** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：induction_on_max (f : ι ->₀ M) (zero : motive 0) (single_add : forall a b 
(f : ι ->₀ M), (forall c in f.support, c < a) -> b != 0 -> motive f -> motive (s
ingle a b + f)) : motive f
参数：f : ι ->₀ M；zero : motive 0；single_add : forall a b (f : ι ->₀ M), (forall c 
in f.support, c < a) -> b != 0 -> motive f -> motive (single a b + f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on_max`：induction_on_max [DecidableEq α] {motive : Fins
et α -> Prop} (s : Finset α) (empty : motive ∅) (insert : forall a s, (forall x 
in s, x < a) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.support_eq_empty`：support_eq_empty {f : α ->₀ M} : f.support = ∅
 ↔ f = 0
· 使用定理 `Finsupp.support_erase`：support_erase [DecidableEq α] {a : α} {f : α ->₀ 
M} : (f.erase a).support = f.support.erase a
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.single_add_erase`：single_add_erase (a : ι) (f : ι ->₀ M) : singl
e a (f a) + f.erase a = f
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s

--- 原说明 ---
A finitely supported function can be built by adding up `single a b` for increas
ing `a`.

The lemma `induction_on_max` swaps the argument order in the sum.
-/
lemma induction_on_max₂ (f : ι →₀ M) (zero : motive 0)
    (add_single : ∀ a b (f : ι →₀ M), (∀ c ∈ f.support, c < a) → b ≠ 0 →
      motive f → motive (f + single a b)) : motive f := by
  refine f.induction_on_max zero ?_
  convert! add_single using 7 with _ _ _ H
  have := fun c hc ↦ (H c hc).ne
  apply (addCommute_of_disjoint _).eq
  simp_all [not_imp_not]

/-- A finitely supported function can be built by adding up `single a b` for decreasing `a`.

The lemma `induction_on_min` swaps the argument order in the sum. -/
/-
**Finsupp.induction_on_min** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：induction_on_min (f : ι ->₀ M) (zero : motive 0) (single_add : forall a b 
(f : ι ->₀ M), (forall c in f.support, a < c) -> b != 0 -> motive f -> motive (s
ingle a b + f)) : motive f
参数：f : ι ->₀ M；zero : motive 0；single_add : forall a b (f : ι ->₀ M), (forall c 
in f.support, a < c) -> b != 0 -> motive f -> motive (single a b + f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.induction_on_max`：induction_on_max (f : ι ->₀ M) (zero : motive 
0) (single_add : forall a b (f : ι ->₀ M), (forall c in f.support, c < a) -> b !
= 0 -> motive …

--- 原说明 ---
A finitely supported function can be built by adding up `single a b` for decreas
ing `a`.

The lemma `induction_on_min` swaps the argument order in the sum.
-/
lemma induction_on_min₂ (f : ι →₀ M) (zero : motive 0)
    (add_single : ∀ a b (f : ι →₀ M), (∀ c ∈ f.support, a < c) → b ≠ 0 →
      motive f → motive (f + single a b)) : motive f :=
  induction_on_max₂ (ι := ιᵒᵈ) f zero add_single

end LinearOrder

end AddZeroClass

section AddMonoid
variable [AddMonoid M]

/-- Note the general `SMul` instance for `Finsupp` doesn't apply as `ℕ` is not distributive
unless `F i`'s addition is commutative. -/
/-
**Finsupp.instNatSMul** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instNatSMul : SMul Nat (ι ->₀ M) where smul n v
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0

--- 原说明 ---
Note the general `SMul` instance for `Finsupp` doesn't apply as `ℕ` is not distr
ibutive
unless `F i`'s addition is commutative.
-/
instance instNatSMul : SMul ℕ (ι →₀ M) where smul n v := v.mapRange (n • ·) (nsmul_zero _)
/-
**Finsupp.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : AddMonoid M] (n : ℕ) (f : ι →₀ M),
 ⇑(n • f) = n • ⇑f
参数：n : ℕ；f : ι →₀ M；n • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_nsmul (n : ℕ) (f : ι →₀ M) : ⇑(n • f) = n • ⇑f := rfl
/-
**Finsupp.nsmul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：nsmul_apply (n : Nat) (f : ι ->₀ M) (x : ι) : (n • f) x = n • f x
参数：n : Nat；f : ι ->₀ M；x : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nsmul_apply (n : ℕ) (f : ι →₀ M) (x : ι) : (n • f) x = n • f x := rfl
/-
**Finsupp.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instAddMonoid : AddMonoid (ι ->₀ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoid : AddMonoid (ι →₀ M) :=
  fast_instance% DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl
/-
**Finsupp.instIsAddTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instIsAddTorsionFree [IsAddTorsionFree M] : IsAddTorsionFree (ι ->₀ M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isAddTorsionFree`：∀ {M : Type u_4} {N : Type u_5} [in
st : AddMonoid M] [inst_1 : AddMonoid N] [IsAddTorsionFree N] (f : M →+ N),   Fu
nction.Injective ⇑f → IsA…
· 使用定理 `Pi.instIsAddTorsionFree`：∀ {ι : Type u_1} {M : ι → Type u_3} [inst : (i 
: ι) → AddMonoid (M i)] [∀ (i : ι), IsAddTorsionFree (M i)],   IsAddTorsionFree 
((i : ι) → M …
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
instance instIsAddTorsionFree [IsAddTorsionFree M] : IsAddTorsionFree (ι →₀ M) :=
  DFunLike.coe_injective.isAddTorsionFree coeFnAddHom

end AddMonoid

section AddCommMonoid
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

/-
**Finsupp.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instAddCommMonoid : AddCommMonoid (ι ->₀ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid : AddCommMonoid (ι →₀ M) :=
  fast_instance% DFunLike.coe_injective.addCommMonoid
    DFunLike.coe coe_zero coe_add (fun _ _ => rfl)
/-
**Finsupp.single_add_single_eq_single_add_single** 是 Mathlib 中的一个引理，位于命名空间 `Fins
upp`。
形式化陈述：single_add_single_eq_single_add_single {k l m n : ι} {u v : M} (hu : u != 
0) (hv : v != 0) : single k u + single l v = single m u + single n v ↔ (k = m ∧ 
l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u + v = 0 ∧ k = l ∧ m = n)
参数：hu : u != 0；hv : v != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.single_eq_pi_single`：single_eq_pi_single [DecidableEq α] (a : α)
 (b : M) : ⇑(single a b) = Pi.single a b
· 使用定理 `Pi.single_add_single_eq_single_add_single`：∀ {I : Type u} [inst : Decida
bleEq I] {M : Type u_5} [inst_1 : AddCommMonoid M] {k l m n : I} {u v : M},   u 
≠ 0 →     v ≠ 0 →       (Pi.sin…
-/
lemma single_add_single_eq_single_add_single {k l m n : ι} {u v : M} (hu : u ≠ 0) (hv : v ≠ 0) :
    single k u + single l v = single m u + single n v ↔
      (k = m ∧ l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u + v = 0 ∧ k = l ∧ m = n) := by
  classical
    simp_rw [DFunLike.ext_iff, coe_add, single_eq_pi_single, ← funext_iff]
    exact Pi.single_add_single_eq_single_add_single hu hv

/-- Composition with a fixed additive homomorphism is itself an additive homomorphism on functions.
-/
@[simps]
/-
**Finsupp.mapRange.addMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.mapRange`。
形式化陈述：{ι : Type u_1} →   {M : Type u_3} →     {N : Type u_4} → [inst : AddCommMo
noid M] → [inst_1 : AddCommMonoid N] → (M →+ N) → (ι →₀ M) →+ ι →₀ N
参数：M →+ N；ι →₀ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition with a fixed additive homomorphism is itself an additive homomorphis
m on functions.
-/
def mapRange.addMonoidHom (f : M →+ N) : (ι →₀ M) →+ ι →₀ N where
  toFun := mapRange f f.map_zero
  map_zero' := mapRange_zero
  map_add' := mapRange_add f.map_add

@[simp]
/-
**Finsupp.mapRange.addMonoidHom_id** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M],   Finsupp.mapRan
ge.addMonoidHom (AddMonoidHom.id M) = AddMonoidHom.id (ι →₀ M)
参数：AddMonoidHom.id M；ι →₀ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Finsupp.mapRange_id`：mapRange_id (g : α ->₀ M) : mapRange id rfl g = g
-/
lemma mapRange.addMonoidHom_id :
    mapRange.addMonoidHom (AddMonoidHom.id M) = AddMonoidHom.id (ι →₀ M) :=
  AddMonoidHom.ext mapRange_id
/-
**Finsupp.mapRange.addMonoidHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange
`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} {O : Type u_5} [inst : AddC
ommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid O] (f : N →+ O
) (g : M →+ N),   Finsupp.mapRange.addMonoidHom (f.comp g) = (Finsupp.mapRange.a
ddMonoidHom f).comp (Finsupp.mapRange.addMonoidHom g)
参数：f : N →+ O；g : M →+ N；f.comp g；Finsupp.mapRange.addMonoidHom f；Finsupp.mapRan
ge.addMonoidHom g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.mapRange.addMonoidHom_apply`：∀ {ι : Type u_1} {M : Type u_3} {N 
: Type u_4} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] (f : M →+ N)   (
g : ι →₀ M), (Finsupp.map…
· 使用引理 `Finsupp.mapRange_mapRange`：mapRange_mapRange (e₁ : N -> O) (e₂ : M -> N)
 (he₁ he₂) (f : α ->₀ M) : mapRange e₁ he₁ (mapRange e₂ he₂ f) = mapRange (e₁ ∘ 
e₂) (by simp [*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRange.addMonoidHom_comp (f : N →+ O) (g : M →+ N) :
    mapRange.addMonoidHom (ι := ι) (f.comp g) =
      (mapRange.addMonoidHom f).comp (mapRange.addMonoidHom g) := by ext; simp

@[simp]
/-
**Finsupp.mapRange.addMonoidHom_toZeroHom** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.map
Range`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommMonoid M] [i
nst_1 : AddCommMonoid N] (f : M →+ N),   ↑(Finsupp.mapRange.addMonoidHom f) = Fi
nsupp.mapRange.zeroHom ↑f
参数：f : M →+ N；Finsupp.mapRange.addMonoidHom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapRange.addMonoidHom_toZeroHom (f : M →+ N) :
    (mapRange.addMonoidHom f).toZeroHom = mapRange.zeroHom (ι := ι) f.toZeroHom := rfl

/-- `Finsupp.mapRange.AddMonoidHom` as an equiv. -/
@[simps! apply]
/-
**Finsupp.mapRange.addEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.mapRange`。
形式化陈述：{ι : Type u_1} →   {M : Type u_3} →     {N : Type u_4} → [inst : AddCommMo
noid M] → [inst_1 : AddCommMonoid N] → M ≃+ N → (ι →₀ M) ≃+ (ι →₀ N)
参数：ι →₀ M；ι →₀ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.mapRange.AddMonoidHom` as an equiv.
-/
def mapRange.addEquiv (em' : M ≃+ N) : (ι →₀ M) ≃+ (ι →₀ N) where
  toEquiv := mapRange.equiv em' em'.map_zero
  __ := mapRange.addMonoidHom em'.toAddMonoidHom

@[simp]
/-
**Finsupp.mapRange.addEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M],   Finsupp.mapRan
ge.addEquiv (AddEquiv.refl M) = AddEquiv.refl (ι →₀ M)
参数：AddEquiv.refl M；ι →₀ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 : A
dd N] {f g : M ≃+ N}, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapRange.addEquiv_apply`：∀ {ι : Type u_1} {M : Type u_3} {N : Ty
pe u_4} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] (em' : M ≃+ N)   (g 
: ι →₀ M), (Finsupp.m…
· 使用定理 `Finsupp.mapRange_id`：mapRange_id (g : α ->₀ M) : mapRange id rfl g = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRange.addEquiv_refl : mapRange.addEquiv (.refl M) = .refl (ι →₀ M) := by ext; simp
/-
**Finsupp.mapRange.addEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} {O : Type u_5} [inst : AddC
ommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid O] (e₁ : M ≃+ 
N) (e₂ : N ≃+ O),   Finsupp.mapRange.addEquiv (e₁.trans e₂) = (Finsupp.mapRange.
addEquiv e₁).trans (Finsupp.mapRange.addEquiv e₂)
参数：e₁ : M ≃+ N；e₂ : N ≃+ O；e₁.trans e₂；Finsupp.mapRange.addEquiv e₁；Finsupp.mapR
ange.addEquiv e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 : A
dd N] {f g : M ≃+ N}, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.mapRange.addEquiv_apply`：∀ {ι : Type u_1} {M : Type u_3} {N : Ty
pe u_4} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] (em' : M ≃+ N)   (g 
: ι →₀ M), (Finsupp.m…
· 使用引理 `Finsupp.mapRange_mapRange`：mapRange_mapRange (e₁ : N -> O) (e₂ : M -> N)
 (he₁ he₂) (f : α ->₀ M) : mapRange e₁ he₁ (mapRange e₂ he₂ f) = mapRange (e₁ ∘ 
e₂) (by simp [*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRange.addEquiv_trans (e₁ : M ≃+ N) (e₂ : N ≃+ O) :
    mapRange.addEquiv (ι := ι) (e₁.trans e₂) =
      (mapRange.addEquiv e₁).trans (mapRange.addEquiv e₂) := by ext; simp

@[simp]
/-
**Finsupp.mapRange.addEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommMonoid M] [i
nst_1 : AddCommMonoid N] (e : M ≃+ N),   (Finsupp.mapRange.addEquiv e).symm = Fi
nsupp.mapRange.addEquiv e.symm
参数：e : M ≃+ N；Finsupp.mapRange.addEquiv e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapRange.addEquiv_symm (e : M ≃+ N) :
    (mapRange.addEquiv (ι := ι) e).symm = mapRange.addEquiv e.symm := rfl

@[simp]
/-
**Finsupp.mapRange.addEquiv_toAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.ma
pRange`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommMonoid M] [i
nst_1 : AddCommMonoid N] (e : M ≃+ N),   ↑(Finsupp.mapRange.addEquiv e) = Finsup
p.mapRange.addMonoidHom e.toAddMonoidHom
参数：e : M ≃+ N；Finsupp.mapRange.addEquiv e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma mapRange.addEquiv_toAddMonoidHom (e : M ≃+ N) :
    mapRange.addEquiv (ι := ι) e = mapRange.addMonoidHom (ι := ι) e.toAddMonoidHom := rfl

@[simp]
/-
**Finsupp.mapRange.addEquiv_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`
。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommMonoid M] [i
nst_1 : AddCommMonoid N] (e : M ≃+ N),   ↑(Finsupp.mapRange.addEquiv e) = Finsup
p.mapRange.equiv ↑e ⋯
参数：e : M ≃+ N；Finsupp.mapRange.addEquiv e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapRange.addEquiv_toEquiv (e : M ≃+ N) :
    mapRange.addEquiv (ι := ι) e = mapRange.equiv (ι := ι) (e : M ≃ N) e.map_zero := rfl

end AddCommMonoid

/-
**Finsupp.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instNeg [NegZeroClass G] : Neg (ι ->₀ G) where neg
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
instance instNeg [NegZeroClass G] : Neg (ι →₀ G) where neg := mapRange Neg.neg neg_zero
/-
**Finsupp.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_6} [inst : NegZeroClass G] (g : ι →₀ G), ⇑(-g
) = -⇑g
参数：g : ι →₀ G；-g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_neg [NegZeroClass G] (g : ι →₀ G) : ⇑(-g) = -g := rfl
/-
**Finsupp.neg_apply** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：neg_apply [NegZeroClass G] (g : ι ->₀ G) (a : ι) : (-g) a = -g a
参数：g : ι ->₀ G；a : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neg_apply [NegZeroClass G] (g : ι →₀ G) (a : ι) : (-g) a = -g a :=
  rfl
/-
**Finsupp.mapRange_neg** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_neg [NegZeroClass G] [NegZeroClass H] {f : G -> H} {hf : f 0 = 0}
 (hf' : forall x, f (-x) = -f x) (v : ι ->₀ G) : mapRange f hf (-v) = -mapRange 
f hf v
参数：hf' : forall x, f (-x) = -f x；v : ι ->₀ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRange_neg [NegZeroClass G] [NegZeroClass H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x, f (-x) = -f x) (v : ι →₀ G) : mapRange f hf (-v) = -mapRange f hf v :=
  ext fun _ => by simp only [hf', neg_apply, mapRange_apply]
/-
**Finsupp.instSub** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instSub [SubNegZeroMonoid G] : Sub (ι ->₀ G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub [SubNegZeroMonoid G] : Sub (ι →₀ G) :=
  ⟨zipWith Sub.sub (sub_zero _)⟩
/-
**Finsupp.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_6} [inst : SubNegZeroMonoid G] (g₁ g₂ : ι →₀ 
G), ⇑(g₁ - g₂) = ⇑g₁ - ⇑g₂
参数：g₁ g₂ : ι →₀ G；g₁ - g₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sub [SubNegZeroMonoid G] (g₁ g₂ : ι →₀ G) : ⇑(g₁ - g₂) = g₁ - g₂ := rfl
/-
**Finsupp.sub_apply** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sub_apply [SubNegZeroMonoid G] (g₁ g₂ : ι ->₀ G) (a : ι) : (g₁ - g₂) a = g
₁ a - g₂ a
参数：g₁ g₂ : ι ->₀ G；a : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sub_apply [SubNegZeroMonoid G] (g₁ g₂ : ι →₀ G) (a : ι) : (g₁ - g₂) a = g₁ a - g₂ a := rfl
/-
**Finsupp.mapRange_sub** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_sub [SubNegZeroMonoid G] [SubNegZeroMonoid H] {f : G -> H} {hf : 
f 0 = 0} (hf' : forall x y, f (x - y) = f x - f y) (v₁ v₂ : ι ->₀ G) : mapRange 
f hf (v₁ - v₂) = mapRange f hf v₁ - mapRange f hf v₂
参数：hf' : forall x y, f (x - y) = f x - f y；v₁ v₂ : ι ->₀ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRange_sub [SubNegZeroMonoid G] [SubNegZeroMonoid H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x y, f (x - y) = f x - f y) (v₁ v₂ : ι →₀ G) :
    mapRange f hf (v₁ - v₂) = mapRange f hf v₁ - mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', sub_apply, mapRange_apply]

section AddGroup
variable [AddGroup G] {p : ι → Prop} {v v' : ι →₀ G}

/-
**Finsupp.mapRange_neg'** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_neg' [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G
 H] {f : F} (v : ι ->₀ G) : mapRange f (map_zero f) (-v) = -mapRange f (map_zero
 f) v
参数：v : ι ->₀ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.mapRange_neg`：mapRange_neg [NegZeroClass G] [NegZeroClass H] {f 
: G -> H} {hf : f 0 = 0} (hf' : forall x, f (-x) = -f x) (v : ι ->₀ G) : mapRang
e f hf (-v…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
-/
lemma mapRange_neg' [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G H]
    {f : F} (v : ι →₀ G) :
    mapRange f (map_zero f) (-v) = -mapRange f (map_zero f) v :=
  mapRange_neg (map_neg f) v
/-
**Finsupp.mapRange_sub'** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_sub' [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G
 H] {f : F} (v₁ v₂ : ι ->₀ G) : mapRange f (map_zero f) (v₁ - v₂) = mapRange f (
map_zero f) v₁ - mapRange f (map_zero f) v₂
参数：v₁ v₂ : ι ->₀ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.mapRange_sub`：mapRange_sub [SubNegZeroMonoid G] [SubNegZeroMonoi
d H] {f : G -> H} {hf : f 0 = 0} (hf' : forall x y, f (x - y) = f x - f y) (v₁ v
₂ : ι ->₀ …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
-/
lemma mapRange_sub' [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G H]
    {f : F} (v₁ v₂ : ι →₀ G) :
    mapRange f (map_zero f) (v₁ - v₂) = mapRange f (map_zero f) v₁ - mapRange f (map_zero f) v₂ :=
  mapRange_sub (map_sub f) v₁ v₂

/-- Note the general `SMul` instance for `Finsupp` doesn't apply as `ℤ` is not distributive
unless `F i`'s addition is commutative. -/
/-
**Finsupp.instIntSMul** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instIntSMul : SMul Int (ι ->₀ G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note the general `SMul` instance for `Finsupp` doesn't apply as `ℤ` is not distr
ibutive
unless `F i`'s addition is commutative.
-/
instance instIntSMul : SMul ℤ (ι →₀ G) :=
  ⟨fun n v => v.mapRange (n • ·) (zsmul_zero _)⟩
/-
**Finsupp.instAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instAddGroup : AddGroup (ι ->₀ G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddGroup : AddGroup (ι →₀ G) :=
  fast_instance% DFunLike.coe_injective.addGroup DFunLike.coe coe_zero coe_add coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

@[simp]
/-
**Finsupp.support_neg** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_neg (f : ι ->₀ G) : support (-f) = support f
参数：f : ι ->₀ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.antisymm`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₁ → s₁ = s₂
· 使用定理 `Finsupp.support_mapRange`：support_mapRange {f : M -> N} {hf : f 0 = 0} {
g : α ->₀ M} : (mapRange f hf g).support subseteq g.support
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma support_neg (f : ι →₀ G) : support (-f) = support f :=
  Finset.Subset.antisymm support_mapRange
    (calc
      support f = support (- -f) := congr_arg support (neg_neg _).symm
      _ ⊆ support (-f) := support_mapRange)
/-
**Finsupp.support_sub** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_sub [DecidableEq ι] {f g : ι ->₀ G} : support (f - g) subseteq sup
port f union support g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.support_neg`：support_neg (f : ι ->₀ G) : support (-f) = support 
f
· 使用引理 `Finsupp.support_add`：support_add [DecidableEq ι] : (g₁ + g₂).support sub
seteq g₁.support union g₂.support
-/
lemma support_sub [DecidableEq ι] {f g : ι →₀ G} : support (f - g) ⊆ support f ∪ support g := by
  rw [sub_eq_add_neg, ← support_neg g]
  exact support_add
/-
**Finsupp.erase_eq_sub_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：erase_eq_sub_single (f : ι ->₀ G) (a : ι) : f.erase a = f - single a (f a)
参数：f : ι ->₀ G；a : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.erase_same`：erase_same {a : α} {f : α ->₀ M} : (f.erase a) a = 0
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.erase_ne`：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.e
rase a) a' = f a'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
lemma erase_eq_sub_single (f : ι →₀ G) (a : ι) : f.erase a = f - single a (f a) := by
  ext a'
  rcases eq_or_ne a' a with (rfl | h)
  · simp
  · simp [h]
/-
**Finsupp.update_eq_sub_add_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：update_eq_sub_add_single (f : ι ->₀ G) (a : ι) (b : G) : f.update a b = f 
- single a (f a) + single a b
参数：f : ι ->₀ G；a : ι；b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.update_eq_erase_add_single`：update_eq_erase_add_single (f : ι ->
₀ M) (a : ι) (b : M) : f.update a b = f.erase a + single a b
· 使用引理 `Finsupp.erase_eq_sub_single`：erase_eq_sub_single (f : ι ->₀ G) (a : ι) :
 f.erase a = f - single a (f a)
-/
lemma update_eq_sub_add_single (f : ι →₀ G) (a : ι) (b : G) :
    f.update a b = f - single a (f a) + single a b := by
  rw [update_eq_erase_add_single, erase_eq_sub_single]

@[simp]
/-
**Finsupp.single_neg** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：single_neg (a : ι) (b : G) : single a (-b) = -single a b
参数：a : ι；b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (a : α), f (-a) = -f a
-/
lemma single_neg (a : ι) (b : G) : single a (-b) = -single a b :=
  (singleAddHom a : G →+ _).map_neg b

@[simp]
/-
**Finsupp.single_sub** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：single_sub (a : ι) (b₁ b₂ : G) : single a (b₁ - b₂) = single a b₁ - single
 a b₂
参数：a : ι；b₁ b₂ : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (g h : α),   f (g - h) = f g - f h
-/
lemma single_sub (a : ι) (b₁ b₂ : G) : single a (b₁ - b₂) = single a b₁ - single a b₂ :=
  (singleAddHom a : G →+ _).map_sub b₁ b₂

@[simp]
/-
**Finsupp.erase_neg** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：erase_neg (a : ι) (f : ι ->₀ G) : erase a (-f) = -erase a f
参数：a : ι；f : ι ->₀ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (a : α), f (-a) = -f a
-/
lemma erase_neg (a : ι) (f : ι →₀ G) : erase a (-f) = -erase a f :=
  (eraseAddHom a : (_ →₀ G) →+ _).map_neg f

@[simp]
/-
**Finsupp.erase_sub** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：erase_sub (a : ι) (f₁ f₂ : ι ->₀ G) : erase a (f₁ - f₂) = erase a f₁ - era
se a f₂
参数：a : ι；f₁ f₂ : ι ->₀ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (g h : α),   f (g - h) = f g - f h
-/
lemma erase_sub (a : ι) (f₁ f₂ : ι →₀ G) : erase a (f₁ - f₂) = erase a f₁ - erase a f₂ :=
  (eraseAddHom a : (_ →₀ G) →+ _).map_sub f₁ f₂

end AddGroup

/-
**Finsupp.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instAddCommGroup [AddCommGroup G] : AddCommGroup (ι ->₀ G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup [AddCommGroup G] : AddCommGroup (ι →₀ G) :=
  fast_instance% DFunLike.coe_injective.addCommGroup DFunLike.coe coe_zero coe_add coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

end Finsupp

