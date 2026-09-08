/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.Weight

/-! # Homogeneous lexicographic monomial ordering

* `MonomialOrder.degLex`: a variant of the lexicographic ordering that first compares degrees.
  For this, `σ` needs to be embedded with an ordering relation which satisfies `WellFoundedGT σ`.
  (This last property is automatic when `σ` is finite).

The type synonym is `DegLex (σ →₀ ℕ)` and the two lemmas `MonomialOrder.degLex_le_iff`
and `MonomialOrder.degLex_lt_iff` rewrite the ordering as comparisons in the type `Lex (σ →₀ ℕ)`.

## References

* [Cox, Little and O'Shea, *Ideals, varieties, and algorithms*][coxlittleoshea1997]
* [Becker and Weispfenning, *Gröbner bases*][Becker-Weispfenning1993]

-/

@[expose] public section

/-- A type synonym to equip a type with its lexicographic order sorted by degrees. -/
/-
**DegLex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DegLex (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym to equip a type with its lexicographic order sorted by degrees.
-/
def DegLex (α : Type*) := α

variable {α : Type*}

/-- `toDegLex` is the identity function to the `DegLex` of a type. -/
/-
**toDegLex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α : Type u_1} → α ≃ DegLex α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`toDegLex` is the identity function to the `DegLex` of a type.
-/
@[match_pattern] def toDegLex : α ≃ DegLex α := Equiv.refl _
/-
**toDegLex_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDegLex_injective : Function.Injective (toDegLex (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toDegLex` is the identity function to the `DegLex` of a type.
-/
theorem toDegLex_injective : Function.Injective (toDegLex (α := α)) := fun _ _ ↦ _root_.id
/-
**toDegLex_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDegLex_inj {a b : α} : toDegLex a = toDegLex b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toDegLex_inj {a b : α} : toDegLex a = toDegLex b ↔ a = b := Iff.rfl

/-- `ofDegLex` is the identity function from the `DegLex` of a type. -/
/-
**ofDegLex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α : Type u_1} → DegLex α ≃ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`ofDegLex` is the identity function from the `DegLex` of a type.
-/
@[match_pattern] def ofDegLex : DegLex α ≃ α := Equiv.refl _
/-
**ofDegLex_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDegLex_injective : Function.Injective (ofDegLex (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofDegLex` is the identity function from the `DegLex` of a type.
-/
theorem ofDegLex_injective : Function.Injective (ofDegLex (α := α)) := fun _ _ ↦ _root_.id
/-
**ofDegLex_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDegLex_inj {a b : DegLex α} : ofDegLex a = ofDegLex b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofDegLex_inj {a b : DegLex α} : ofDegLex a = ofDegLex b ↔ a = b := Iff.rfl
/-
**ofDegLex_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1}, ofDegLex.symm = toDegLex
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem ofDegLex_symm_eq : (@ofDegLex α).symm = toDegLex := rfl
/-
**toDegLex_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1}, toDegLex.symm = ofDegLex
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem toDegLex_symm_eq : (@toDegLex α).symm = ofDegLex := rfl
/-
**ofDegLex_toDegLex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} (a : α), ofDegLex (toDegLex a) = a
参数：a : α；toDegLex a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofDegLex_toDegLex (a : α) : ofDegLex (toDegLex a) = a := rfl
/-
**toDegLex_ofDegLex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} (a : DegLex α), toDegLex (ofDegLex a) = a
参数：a : DegLex α；ofDegLex a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toDegLex_ofDegLex (a : DegLex α) : toDegLex (ofDegLex a) = a := rfl

/-- A recursor for `DegLex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/-
**DegLex.rec** 是 Mathlib 中的一个定义，位于命名空间 `DegLex`。
形式化陈述：{α : Type u_1} → {β : DegLex α → Sort u_2} → ((a : α) → β (toDegLex a)) → 
(a : DegLex α) → β a
参数：(a : α) → β (toDegLex a)；a : DegLex α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for `DegLex`. Use as `induction x`.
-/
protected def DegLex.rec {β : DegLex α → Sort*} (h : ∀ a, β (toDegLex a)) :
    ∀ a, β a := fun a => h (ofDegLex a)
/-
**DegLex.forall_iff** 是 Mathlib 中的一个定理，位于命名空间 `DegLex`。
形式化陈述：∀ {α : Type u_1} {p : DegLex α → Prop}, (∀ (a : DegLex α), p a) ↔ ∀ (a : α
), p (toDegLex a)
参数：∀ (a : DegLex α), p a；a : α；toDegLex a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma DegLex.forall_iff {p : DegLex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toDegLex a) := Iff.rfl
/-
**DegLex.exists_iff** 是 Mathlib 中的一个定理，位于命名空间 `DegLex`。
形式化陈述：∀ {α : Type u_1} {p : DegLex α → Prop}, (∃ a, p a) ↔ ∃ a, p (toDegLex a)
参数：∃ a, p a；toDegLex a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma DegLex.exists_iff {p : DegLex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toDegLex a) := Iff.rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [AddCommMonoid α] :
    AddCommMonoid (DegLex α) := ofDegLex.addCommMonoid
/-
**toDegLex_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDegLex_add [AddCommMonoid α] (a b : α) : toDegLex (a + b) = toDegLex a +
 toDegLex b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDegLex_add [AddCommMonoid α] (a b : α) :
    toDegLex (a + b) = toDegLex a + toDegLex b := rfl
/-
**ofDegLex_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDegLex_add [AddCommMonoid α] (a b : DegLex α) : ofDegLex (a + b) = ofDeg
Lex a + ofDegLex b
参数：a b : DegLex α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDegLex_add [AddCommMonoid α] (a b : DegLex α) :
    ofDegLex (a + b) = ofDegLex a + ofDegLex b := rfl

namespace Finsupp

open scoped Function in -- required for scoped `on` notation
/-- `Finsupp.DegLex r s` is the homogeneous lexicographic order on `α →₀ M`,
where `α` is ordered by `r` and `M` is ordered by `s`.
The type synonym `DegLex (α →₀ M)` has an order given by `Finsupp.DegLex (· < ·) (· < ·)`. -/
/-
**Finsupp.DegLex** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：{α : Type u_1} → (α → α → Prop) → (ℕ → ℕ → Prop) → (α →₀ ℕ) → (α →₀ ℕ) → P
rop
参数：α → α → Prop；ℕ → ℕ → Prop；α →₀ ℕ；α →₀ ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.DegLex r s` is the homogeneous lexicographic order on `α →₀ M`,
where `α` is ordered by `r` and `M` is ordered by `s`.
The type synonym `DegLex (α →₀ M)` has an order given by `Finsupp.DegLex (· < ·)
 (· < ·)`.
-/
protected def DegLex (r : α → α → Prop) (s : ℕ → ℕ → Prop) :
    (α →₀ ℕ) → (α →₀ ℕ) → Prop :=
  (Prod.Lex s (Finsupp.Lex r s)) on (fun x ↦ (x.degree, x))
/-
**Finsupp.degLex_def** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：degLex_def {r : α -> α -> Prop} {s : Nat -> Nat -> Prop} {a b : α ->₀ Nat}
 : Finsupp.DegLex r s a b ↔ Prod.Lex s (Finsupp.Lex r s) (a.degree, a) (b.degree
, b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem degLex_def {r : α → α → Prop} {s : ℕ → ℕ → Prop} {a b : α →₀ ℕ} :
    Finsupp.DegLex r s a b ↔ Prod.Lex s (Finsupp.Lex r s) (a.degree, a) (b.degree, b) :=
  Iff.rfl

namespace DegLex

/-
**Finsupp.DegLex.wellFounded** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.DegLex`。
形式化陈述：wellFounded {r : α -> α -> Prop} [Std.Trichotomous r] (hr : WellFounded (F
unction.swap r)) {s : Nat -> Nat -> Prop} (hs : WellFounded s) (hs0 : forall ⦃n⦄
, ¬ s n 0) : WellFounded (Finsupp.DegLex r s)
参数：hr : WellFounded (Function.swap r)；hs : WellFounded s；hs0 : forall ⦃n⦄, ¬ s n
 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WellFounded.prod_lex`：WellFounded.prod_lex {ra : α -> α -> Prop} {rb : β
 -> β -> Prop} (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (Prod.L
ex ra rb)
· 使用定理 `Finsupp.Lex.wellFounded'`：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N
] {r : α → α → Prop} {s : N → N → Prop},   (∀ ⦃n : N⦄, ¬s n 0) →     WellFounded
 s → ∀ [Std.Tr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.wellFoundedOn_range`：wellFoundedOn_range : (range f).WellFoundedOn r
 ↔ WellFounded (r on f)
· 使用定理 `Set.WellFoundedOn.mono`：∀ {α : Type u_2} {r r' : α → α → Prop} {s t : Se
t α}, t.WellFoundedOn r' → r ≤ r' → s ⊆ t → s.WellFoundedOn r
· 使用定理 `Set.wellFoundedOn_univ`：wellFoundedOn_univ : (univ : Set α).WellFoundedO
n r ↔ WellFounded r
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `trivial`：True
-/
theorem wellFounded
    {r : α → α → Prop} [Std.Trichotomous r] (hr : WellFounded (Function.swap r))
    {s : ℕ → ℕ → Prop} (hs : WellFounded s) (hs0 : ∀ ⦃n⦄, ¬ s n 0) :
    WellFounded (Finsupp.DegLex r s) := by
  have wft := WellFounded.prod_lex hs (Finsupp.Lex.wellFounded' hs0 hs hr)
  rw [← Set.wellFoundedOn_univ] at wft
  unfold Finsupp.DegLex
  rw [← Set.wellFoundedOn_range]
  exact Set.WellFoundedOn.mono wft (le_refl _) (fun _ _ ↦ trivial)
/-
**Finsupp.DegLex.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp.DegLex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT α] : LT (DegLex (α →₀ ℕ)) :=
  ⟨fun f g ↦ Finsupp.DegLex (· < ·) (· < ·) (ofDegLex f) (ofDegLex g)⟩
/-
**Finsupp.DegLex.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.DegLex`。
形式化陈述：lt_def [LT α] {a b : DegLex (α ->₀ Nat)} : a < b ↔ (toLex ((ofDegLex a).de
gree, toLex (ofDegLex a))) < (toLex ((ofDegLex b).degree, toLex (ofDegLex b)))
参数：α ->₀ Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_def [LT α] {a b : DegLex (α →₀ ℕ)} :
    a < b ↔ (toLex ((ofDegLex a).degree, toLex (ofDegLex a))) <
        (toLex ((ofDegLex b).degree, toLex (ofDegLex b))) :=
  Iff.rfl
/-
**Finsupp.DegLex.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.DegLex`。
形式化陈述：lt_iff [LT α] {a b : DegLex (α ->₀ Nat)} : a < b ↔ (ofDegLex a).degree < (
ofDegLex b).degree ∨ (((ofDegLex a).degree = (ofDegLex b).degree) ∧ toLex (ofDeg
Lex a) < toLex (ofDegLex b))
参数：α ->₀ Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_iff [LT α] {a b : DegLex (α →₀ ℕ)} :
    a < b ↔ (ofDegLex a).degree < (ofDegLex b).degree ∨
    (((ofDegLex a).degree = (ofDegLex b).degree) ∧ toLex (ofDegLex a) < toLex (ofDegLex b)) := by
  simp [lt_def, Prod.Lex.toLex_lt_toLex]

variable [LinearOrder α]
/-
**Finsupp.DegLex.isStrictOrder** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp.DegLex`。
形式化陈述：isStrictOrder : IsStrictOrder (DegLex (α ->₀ Nat)) (· < ·) where irrefl
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `lt_of_lt_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lt_of_eq_of_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < 
c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance isStrictOrder : IsStrictOrder (DegLex (α →₀ ℕ)) (· < ·) where
  irrefl := fun a ↦ by simp [lt_def]
  trans := by
    intro a b c hab hbc
    simp only [lt_iff] at hab hbc ⊢
    rcases hab with (hab | hab)
    · rcases hbc with (hbc | hbc)
      · left; exact lt_trans hab hbc
      · left; exact lt_of_lt_of_eq hab hbc.1
    · rcases hbc with (hbc | hbc)
      · left; exact lt_of_eq_of_lt hab.1 hbc
      · right; exact ⟨Eq.trans hab.1 hbc.1, lt_trans hab.2 hbc.2⟩

/-- The linear order on `Finsupp`s obtained by the homogeneous lexicographic ordering. -/
/-
**Finsupp.DegLex.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp.DegLex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear order on `Finsupp`s obtained by the homogeneous lexicographic orderin
g.
-/
noncomputable instance : LinearOrder (DegLex (α →₀ ℕ)) :=
  fast_instance% LinearOrder.lift'
    (fun (f : DegLex (α →₀ ℕ)) ↦ toLex ((ofDegLex f).degree, toLex (ofDegLex f)))
    (fun f g ↦ by simp)
/-
**Finsupp.DegLex.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.DegLex`。
形式化陈述：le_iff {x y : DegLex (α ->₀ Nat)} : x <= y ↔ (ofDegLex x).degree < (ofDegL
ex y).degree ∨ (ofDegLex x).degree = (ofDegLex y).degree ∧ toLex (ofDegLex x) <=
 toLex (ofDegLex y)
参数：α ->₀ Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem le_iff {x y : DegLex (α →₀ ℕ)} :
    x ≤ y ↔ (ofDegLex x).degree < (ofDegLex y).degree ∨
      (ofDegLex x).degree = (ofDegLex y).degree ∧ toLex (ofDegLex x) ≤ toLex (ofDegLex y) := by
  simp only [le_iff_eq_or_lt, lt_iff, EmbeddingLike.apply_eq_iff_eq]
  by_cases h : x = y
  · simp [h]
  · by_cases k : (ofDegLex x).degree < (ofDegLex y).degree
    · simp [k]
    · simp only [h, k, false_or]
/-
**Finsupp.DegLex.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp.DegLex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedCancelAddMonoid (DegLex (α →₀ ℕ)) where
  le_of_add_le_add_left a b c h := by
    rw [le_iff] at h ⊢
    simpa only [ofDegLex_add, map_add, add_lt_add_iff_left, add_right_inj, toLex_add,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [le_iff] at h ⊢
    simpa [ofDegLex_add, map_add] using h
/-
**Finsupp.DegLex.single_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.DegLex`。
形式化陈述：single_strictAnti : StrictAnti (fun (a : α) => toDegLex (single a 1))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_single`：degree_single (a : σ) (r : R) : (Finsupp.single a
 r).degree = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem single_strictAnti : StrictAnti (fun (a : α) ↦ toDegLex (single a 1)) := by
  intro _ _ h
  simp only [lt_iff, ofDegLex_toDegLex, degree_single, lt_self_iff_false, Lex.single_lt_iff, h,
    and_self, or_true]
/-
**Finsupp.DegLex.single_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.DegLex`。
形式化陈述：single_antitone : Antitone (fun (a : α) => toDegLex (single a 1))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.antitone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictAnti f → Antitone f
· 使用定理 `Finsupp.DegLex.single_strictAnti`：single_strictAnti : StrictAnti (fun (a
 : α) => toDegLex (single a 1))
-/
theorem single_antitone : Antitone (fun (a : α) ↦ toDegLex (single a 1)) :=
  single_strictAnti.antitone
/-
**Finsupp.DegLex.single_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.DegLex`。
形式化陈述：single_lt_iff {a b : α} : toDegLex (Finsupp.single b 1) < toDegLex (Finsup
p.single a 1) ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.lt_iff_gt`：StrictAnti.lt_iff_gt (hf : StrictAnti f) {a b : α}
 : f a < f b ↔ b < a
· 使用定理 `Finsupp.DegLex.single_strictAnti`：single_strictAnti : StrictAnti (fun (a
 : α) => toDegLex (single a 1))
-/
theorem single_lt_iff {a b : α} :
    toDegLex (Finsupp.single b 1) < toDegLex (Finsupp.single a 1) ↔ a < b :=
  single_strictAnti.lt_iff_gt
/-
**Finsupp.DegLex.single_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.DegLex`。
形式化陈述：single_le_iff {a b : α} : toDegLex (Finsupp.single b 1) <= toDegLex (Finsu
pp.single a 1) ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.le_iff_ge`：StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α}
 : f a <= f b ↔ b <= a
· 使用定理 `Finsupp.DegLex.single_strictAnti`：single_strictAnti : StrictAnti (fun (a
 : α) => toDegLex (single a 1))
-/
theorem single_le_iff {a b : α} :
    toDegLex (Finsupp.single b 1) ≤ toDegLex (Finsupp.single a 1) ↔ a ≤ b :=
  single_strictAnti.le_iff_ge
/-
**Finsupp.DegLex.monotone_degree** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.DegLex`。
形式化陈述：monotone_degree : Monotone (fun (x : DegLex (α ->₀ Nat)) => (ofDegLex x).d
egree)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.DegLex.le_iff`：le_iff {x y : DegLex (α ->₀ Nat)} : x <= y ↔ (ofD
egLex x).degree < (ofDegLex y).degree ∨ (ofDegLex x).degree = (ofDegLex y).degre
e ∧ toLex (…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem monotone_degree :
    Monotone (fun (x : DegLex (α →₀ ℕ)) ↦ (ofDegLex x).degree) := by
  intro x y
  rw [le_iff]
  rintro (h | h)
  · apply le_of_lt h
  · apply le_of_eq h.1
/-
**Finsupp.DegLex.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp.DegLex`。
形式化陈述：orderBot : OrderBot (DegLex (α ->₀ Nat)) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance orderBot : OrderBot (DegLex (α →₀ ℕ)) where
  bot := toDegLex (0 : α →₀ ℕ)
  bot_le x := by
    simp only [le_iff, ofDegLex_toDegLex, toLex_zero, map_zero]
    rcases eq_zero_or_pos (ofDegLex x).degree with (h | h)
    · simp only [h, lt_self_iff_false, true_and, false_or]
      exact bot_le
    · simp [h]
/-
**Finsupp.DegLex.wellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp.DegLex`。
形式化陈述：wellFoundedLT [WellFoundedGT α] : WellFoundedLT (DegLex (α ->₀ Nat))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.DegLex.wellFounded`：wellFounded {r : α -> α -> Prop} [Std.Tricho
tomous r] (hr : WellFounded (Function.swap r)) {s : Nat -> Nat -> Prop} (hs : We
llFounded s) (hs…
· 使用定理 `wellFounded_gt`：∀ {α : Type u} [inst : LT α] [WellFoundedGT α], WellFoun
ded fun x1 x2 => x2 < x1
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `not_lt_zero`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], ¬a < 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
instance wellFoundedLT [WellFoundedGT α] : WellFoundedLT (DegLex (α →₀ ℕ)) :=
  ⟨wellFounded wellFounded_gt wellFounded_lt fun _ ↦ not_lt_zero⟩

end DegLex

end Finsupp

namespace MonomialOrder

open Finsupp

variable {σ : Type*} [LinearOrder σ] [WellFoundedGT σ]

/-- The deg-lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder` -/
/-
**MonomialOrder.degLex** 是 Mathlib 中的一个定义，位于命名空间 `MonomialOrder`。
形式化陈述：degLex : MonomialOrder σ where syn
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The deg-lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder`
-/
noncomputable def degLex :
    MonomialOrder σ where
  syn := DegLex (σ →₀ ℕ)
  toSyn := { toEquiv := toDegLex, map_add' := toDegLex_add }
  toSyn_monotone a b h := by
    simp only [AddEquiv.coe_mk, DegLex.le_iff, ofDegLex_toDegLex]
    by_cases! ha : a.degree < b.degree
    · exact Or.inl ha
    · refine Or.inr ⟨le_antisymm ?_ ha, toLex_monotone h⟩
      rw [← add_tsub_cancel_of_le h, map_add]
      exact Nat.le_add_right a.degree (b - a).degree
/-
**MonomialOrder.degLex_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degLex_le_iff {a b : σ ->₀ Nat} : a ≼[degLex] b ↔ toDegLex a <= toDegLex b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem degLex_le_iff {a b : σ →₀ ℕ} :
    a ≼[degLex] b ↔ toDegLex a ≤ toDegLex b :=
  Iff.rfl
/-
**MonomialOrder.degLex_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degLex_lt_iff {a b : σ ->₀ Nat} : a ≺[degLex] b ↔ toDegLex a < toDegLex b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem degLex_lt_iff {a b : σ →₀ ℕ} :
    a ≺[degLex] b ↔ toDegLex a < toDegLex b :=
  Iff.rfl
/-
**MonomialOrder.degLex_single_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degLex_single_le_iff {a b : σ} : single a 1 ≼[degLex] single b 1 ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degLex_le_iff`：degLex_le_iff {a b : σ ->₀ Nat} : a ≼[degLe
x] b ↔ toDegLex a <= toDegLex b
· 使用定理 `Finsupp.DegLex.single_le_iff`：single_le_iff {a b : α} : toDegLex (Finsup
p.single b 1) <= toDegLex (Finsupp.single a 1) ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem degLex_single_le_iff {a b : σ} :
    single a 1 ≼[degLex] single b 1 ↔ b ≤ a := by
  rw [MonomialOrder.degLex_le_iff, DegLex.single_le_iff]
/-
**MonomialOrder.degLex_single_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degLex_single_lt_iff {a b : σ} : single a 1 ≺[degLex] single b 1 ↔ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degLex_lt_iff`：degLex_lt_iff {a b : σ ->₀ Nat} : a ≺[degLe
x] b ↔ toDegLex a < toDegLex b
· 使用定理 `Finsupp.DegLex.single_lt_iff`：single_lt_iff {a b : α} : toDegLex (Finsup
p.single b 1) < toDegLex (Finsupp.single a 1) ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem degLex_single_lt_iff {a b : σ} :
    single a 1 ≺[degLex] single b 1 ↔ b < a := by
  rw [MonomialOrder.degLex_lt_iff, DegLex.single_lt_iff]

end MonomialOrder

section Examples

open Finsupp MonomialOrder DegLex

/-- for the deg-lexicographic ordering, X 1 < X 0 -/
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
for the deg-lexicographic ordering, X 1 < X 0
-/
example : single (1 : Fin 2) 1 ≺[degLex] single 0 1 := by
  rw [degLex_lt_iff, single_lt_iff]
  exact Nat.one_pos

/-- for the deg-lexicographic ordering, X 0 * X 1 < X 0  ^ 2 -/
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
for the deg-lexicographic ordering, X 0 * X 1 < X 0  ^ 2
-/
example : (single 0 1 + single 1 1) ≺[degLex] single (0 : Fin 2) 2 := by
  rw [degLex_lt_iff, lt_iff, ofDegLex_toDegLex]
  simp only [Fin.isValue, map_add, degree_single, Nat.reduceAdd, ofDegLex_toDegLex,
    lt_self_iff_false, toLex_add, true_and, false_or]
  use 0
  simp

/-- for the deg-lexicographic ordering, X 0 < X 1 ^ 2 -/
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
for the deg-lexicographic ordering, X 0 < X 1 ^ 2
-/
example : single (0 : Fin 2) 1 ≺[degLex] single 1 2 := by
  simp [degLex_lt_iff, lt_iff]

end Examples

