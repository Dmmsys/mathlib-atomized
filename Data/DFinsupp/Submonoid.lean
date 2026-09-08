/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# `DFinsupp` and submonoids

This file mainly concerns the interaction between submonoids and products/sums of `DFinsupp`s.

## Main results

* `AddSubmonoid.mem_iSup_iff_exists_dfinsupp`: elements of the supremum of additive commutative
  monoids can be given by taking finite sums of elements of each monoid.
* `AddSubmonoid.mem_bsupr_iff_exists_dfinsupp`: elements of the supremum of additive commutative
  monoids can be given by taking finite sums of elements of each monoid.
-/

public section


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

open DFinsupp

variable [DecidableEq ι]

@[to_additive]
/-
**dfinsuppProd_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dfinsuppProd_mem [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (
x != 0)] [CommMonoid γ] {S : Type*} [SetLike S γ] [SubmonoidClass S γ] (s : S) (
f : Π₀ i, β i) (g : forall i, β i -> γ) (h : forall c, f c != 0 -> g c (f c) in 
s) : f.prod g in s
参数：β i；i；x : β i；x != 0；s : S；f : Π₀ i, β i；g : forall i, β i -> γ；h : forall c,
 f c != 0 -> g c (f c) in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prod_mem`：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidCl
ass B M] {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFinsupp.mem_support_iff`：mem_support_iff {f : Π₀ i, β i} {i : ι} : i in
 f.support ↔ f i != 0
-/
theorem dfinsuppProd_mem [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {S : Type*} [SetLike S γ] [SubmonoidClass S γ]
    (s : S) (f : Π₀ i, β i) (g : ∀ i, β i → γ)
    (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.prod g ∈ s :=
  prod_mem fun _ hi => h _ <| mem_support_iff.1 hi
/-
**dfinsuppSumAddHom_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dfinsuppSumAddHom_mem [forall i, AddZeroClass (β i)] [AddCommMonoid γ] {S 
: Type*} [SetLike S γ] [AddSubmonoidClass S γ] (s : S) (f : Π₀ i, β i) (g : fora
ll i, β i ->+ γ) (h : forall c, f c != 0 -> g c (f c) in s) : DFinsupp.sumAddHom
 g f in s
参数：β i；s : S；f : Π₀ i, β i；g : forall i, β i ->+ γ；h : forall c, f c != 0 -> g c
 (f c) in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
· 使用定理 `dfinsuppSum_mem`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst : De
cidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x : β i) → D
ecida…
-/
theorem dfinsuppSumAddHom_mem [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] {S : Type*}
    [SetLike S γ] [AddSubmonoidClass S γ] (s : S) (f : Π₀ i, β i) (g : ∀ i, β i →+ γ)
    (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : DFinsupp.sumAddHom g f ∈ s := by
  classical
    rw [DFinsupp.sumAddHom_apply]
    exact dfinsuppSum_mem s f (g ·) h

/-- The supremum of a family of commutative additive submonoids is equal to the range of
`DFinsupp.sumAddHom`; that is, every element in the `iSup` can be produced from taking a finite
number of non-zero elements of `S i`, coercing them to `γ`, and summing them. -/
/-
**AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom [AddCommMonoid γ] (S : ι -> 
AddSubmonoid γ) : iSup S = AddMonoidHom.mrange (DFinsupp.sumAddHom fun i => (S i
).subtype)
参数：S : ι -> AddSubmonoid γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
· 使用定理 `dfinsuppSumAddHom_mem`：dfinsuppSumAddHom_mem [forall i, AddZeroClass (β 
i)] [AddCommMonoid γ] {S : Type*} [SetLike S γ] [AddSubmonoidClass S γ] (s : S) 
(f : Π₀ i, …
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
The supremum of a family of commutative additive submonoids is equal to the rang
e of
`DFinsupp.sumAddHom`; that is, every element in the `iSup` can be produced from 
taking a finite
number of non-zero elements of `S i`, coercing them to `γ`, and summing them.
-/
theorem AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom
    [AddCommMonoid γ] (S : ι → AddSubmonoid γ) :
    iSup S = AddMonoidHom.mrange (DFinsupp.sumAddHom fun i => (S i).subtype) := by
  apply le_antisymm
  · apply iSup_le _
    intro i y hy
    exact ⟨DFinsupp.single i ⟨y, hy⟩, DFinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsuppSumAddHom_mem _ v _ fun i _ => (le_iSup S i : S i ≤ _) (v i).prop

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`DFinsupp.sumAddHom` composed with `DFinsupp.filterAddMonoidHom`; that is, every element in the
bounded `iSup` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
/-
**AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom (p : ι -> Prop) [DecidableP
red p] [AddCommMonoid γ] (S : ι -> AddSubmonoid γ) : ⨆ (i) (_ : p i), S i = AddM
onoidHom.mrange ((sumAddHom fun i => (S i).subtype).comp (filterAddMonoidHom _ p
))
参数：p : ι -> Prop；S : ι -> AddSubmonoid γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.comp_apply`：∀ {M : Type u_4} {N : Type u_5} {P : Type u_6} 
[inst : AddZero M] [inst_1 : AddZero N] [inst_2 : AddZero P] (g : N →+ P)   (f :
 M →+ N) (x :…
· 使用定理 `DFinsupp.filterAddMonoidHom_apply`：∀ {ι : Type u} (β : ι → Type v) [inst
 : (i : ι) → AddZeroClass (β i)] (p : ι → Prop) [inst_1 : DecidablePred p]   (x 
: Π₀ (i : ι), β i), (DF…
· 使用定理 `DFinsupp.filter_single_pos`：filter_single_pos {p : ι -> Prop} [Decidable
Pred p] (i : ι) (x : β i) (h : p i) : (single i x).filter p = single i x
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
· 使用定理 `dfinsuppSumAddHom_mem`：dfinsuppSumAddHom_mem [forall i, AddZeroClass (β 
i)] [AddCommMonoid γ] {S : Type*} [SetLike S γ] [AddSubmonoidClass S γ] (s : S) 
(f : Π₀ i, …
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `AddSubmonoid.mem_iSup_of_mem`：∀ {M : Type u_1} [inst : AddZeroClass M] {
ι : Sort u_4} {S : ι → AddSubmonoid M} (i : ι) {x : M}, x ∈ S i → x ∈ iSup S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M

--- 原说明 ---
The bounded supremum of a family of commutative additive submonoids is equal to 
the range of
`DFinsupp.sumAddHom` composed with `DFinsupp.filterAddMonoidHom`; that is, every
 element in the
bounded `iSup` can be produced from taking a finite number of non-zero elements 
from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them.
-/
theorem AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom (p : ι → Prop) [DecidablePred p]
    [AddCommMonoid γ] (S : ι → AddSubmonoid γ) :
    ⨆ (i) (_ : p i), S i =
      AddMonoidHom.mrange ((sumAddHom fun i => (S i).subtype).comp (filterAddMonoidHom _ p)) := by
  apply le_antisymm
  · refine iSup₂_le fun i hi y hy => ⟨DFinsupp.single i ⟨y, hy⟩, ?_⟩
    rw [AddMonoidHom.comp_apply, filterAddMonoidHom_apply, filter_single_pos _ _ hi]
    exact sumAddHom_single _ _ _
  · rintro x ⟨v, rfl⟩
    refine dfinsuppSumAddHom_mem _ _ _ fun i _ => ?_
    refine AddSubmonoid.mem_iSup_of_mem i ?_
    by_cases hp : p i
    · simp [hp]
    · simp [hp]
/-
**AddSubmonoid.mem_iSup_iff_exists_dfinsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.mem_iSup_iff_exists_dfinsupp [AddCommMonoid γ] (S : ι -> AddS
ubmonoid γ) (x : γ) : x in iSup S ↔ exists f : Π₀ i, S i, DFinsupp.sumAddHom (fu
n i => (S i).subtype) f = x
参数：S : ι -> AddSubmonoid γ；x : γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom`：AddSubmonoid.iSup_eq_mran
ge_dfinsuppSumAddHom [AddCommMonoid γ] (S : ι -> AddSubmonoid γ) : iSup S = AddM
onoidHom.mrange (DFinsupp.sumAddHom…
-/
theorem AddSubmonoid.mem_iSup_iff_exists_dfinsupp [AddCommMonoid γ] (S : ι → AddSubmonoid γ)
    (x : γ) : x ∈ iSup S ↔ ∃ f : Π₀ i, S i, DFinsupp.sumAddHom (fun i => (S i).subtype) f = x :=
  SetLike.ext_iff.mp (AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom S) x

/-- A variant of `AddSubmonoid.mem_iSup_iff_exists_dfinsupp` with the RHS fully unfolded. -/
/-
**AddSubmonoid.mem_iSup_iff_exists_dfinsupp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.mem_iSup_iff_exists_dfinsupp' [AddCommMonoid γ] (S : ι -> Add
Submonoid γ) [forall (i) (x : S i), Decidable (x != 0)] (x : γ) : x in iSup S ↔ 
exists f : Π₀ i, S i, (f.sum fun _ xi => ↑xi) = x
参数：S : ι -> AddSubmonoid γ；i；x : S i；x != 0；x : γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoid.mem_iSup_iff_exists_dfinsupp`：AddSubmonoid.mem_iSup_iff_exi
sts_dfinsupp [AddCommMonoid γ] (S : ι -> AddSubmonoid γ) (x : γ) : x in iSup S ↔
 exists f : Π₀ i, S i, DFinsupp…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A variant of `AddSubmonoid.mem_iSup_iff_exists_dfinsupp` with the RHS fully unfo
lded.
-/
theorem AddSubmonoid.mem_iSup_iff_exists_dfinsupp' [AddCommMonoid γ] (S : ι → AddSubmonoid γ)
    [∀ (i) (x : S i), Decidable (x ≠ 0)] (x : γ) :
    x ∈ iSup S ↔ ∃ f : Π₀ i, S i, (f.sum fun _ xi => ↑xi) = x := by
  rw [AddSubmonoid.mem_iSup_iff_exists_dfinsupp]
  simp_rw [sumAddHom_apply]
  rfl
/-
**AddSubmonoid.mem_bsupr_iff_exists_dfinsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.mem_bsupr_iff_exists_dfinsupp (p : ι -> Prop) [DecidablePred 
p] [AddCommMonoid γ] (S : ι -> AddSubmonoid γ) (x : γ) : (x in ⨆ (i) (_ : p i), 
S i) ↔ exists f : Π₀ i, S i, DFinsupp.sumAddHom (fun i => (S i).subtype) (f.filt
er p) = x
参数：p : ι -> Prop；S : ι -> AddSubmonoid γ；x : γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom`：AddSubmonoid.bsupr_eq_mr
ange_dfinsuppSumAddHom (p : ι -> Prop) [DecidablePred p] [AddCommMonoid γ] (S : 
ι -> AddSubmonoid γ) : ⨆ (i) (_ : p …
-/
theorem AddSubmonoid.mem_bsupr_iff_exists_dfinsupp (p : ι → Prop) [DecidablePred p]
    [AddCommMonoid γ] (S : ι → AddSubmonoid γ) (x : γ) :
    (x ∈ ⨆ (i) (_ : p i), S i) ↔
      ∃ f : Π₀ i, S i, DFinsupp.sumAddHom (fun i => (S i).subtype) (f.filter p) = x :=
  SetLike.ext_iff.mp (AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom p S) x
