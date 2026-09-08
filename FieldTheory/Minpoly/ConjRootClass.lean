/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.FieldTheory.Minpoly.IsConjRoot

/-!
# Conjugate root classes

In this file, we define the `ConjRootClass` of a field extension `L / K` as the quotient of `L` by
the relation `IsConjRoot K`.
-/

@[expose] public section

variable (K L S : Type*) [Field K] [Field L] [Field S]
variable [Algebra K L] [Algebra K S] [Algebra L S] [IsScalarTower K L S]

/-- `ConjRootClass K L` is the quotient of `L` by the relation `IsConjRoot K`. -/
/-
**ConjRootClass** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ConjRootClass
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ConjRootClass K L` is the quotient of `L` by the relation `IsConjRoot K`.
-/
def ConjRootClass := Quotient (α := L) (IsConjRoot.setoid K L)

namespace ConjRootClass

variable {L}

/-- The canonical quotient map from a field `K` into the `ConjRootClass` of the field extension
`L / K`. -/
/-
**ConjRootClass.mk** 是 Mathlib 中的一个定义，位于命名空间 `ConjRootClass`。
形式化陈述：mk (x : L) : ConjRootClass K L
参数：x : L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical quotient map from a field `K` into the `ConjRootClass` of the fiel
d extension
`L / K`.
-/
def mk (x : L) : ConjRootClass K L :=
  ⟦x⟧

@[simp]
/-
**ConjRootClass.mk_def** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：mk_def {x : L} : ⟦x⟧ = mk K x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_def {x : L} : ⟦x⟧ = mk K x := rfl
/-
**ConjRootClass.** 是 Mathlib 中的一个实例，位于命名空间 `ConjRootClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (ConjRootClass K L) :=
  ⟨mk K 0⟩

@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**ConjRootClass.ind** 是 Mathlib 中的一个引理，位于命名空间 `ConjRootClass`。
形式化陈述：ind {motive : ConjRootClass K L -> Prop} (h : forall x : L, motive (mk K x
)) (c : ConjRootClass K L) : motive c
参数：h : forall x : L, motive (mk K x)；c : ConjRootClass K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
-/
lemma ind {motive : ConjRootClass K L → Prop} (h : ∀ x : L, motive (mk K x))
    (c : ConjRootClass K L) : motive c :=
  Quotient.ind h c

variable {K}

@[simp]
/-
**ConjRootClass.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：mk_eq_mk {x y : L} : mk K x = mk K y ↔ IsConjRoot K x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
theorem mk_eq_mk {x y : L} : mk K x = mk K y ↔ IsConjRoot K x y := Quotient.eq

@[simp]
/-
**ConjRootClass.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：mk_zero : mk K (0 : L) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_zero : mk K (0 : L) = 0 :=
  rfl

@[simp]
/-
**ConjRootClass.mk_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：mk_eq_zero_iff (x : L) : mk K x = 0 ↔ x = 0
参数：x : L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ConjRootClass.mk_zero`：mk_zero : mk K (0 : L) = 0
· 使用定理 `ConjRootClass.mk_eq_mk`：mk_eq_mk {x y : L} : mk K x = mk K y ↔ IsConjRoo
t K x y
· 使用定理 `isConjRoot_zero_iff_eq_zero`：isConjRoot_zero_iff_eq_zero {x : S} : IsCon
jRoot K 0 x ↔ x = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_eq_zero_iff (x : L) : mk K x = 0 ↔ x = 0 := by
  rw [eq_comm (b := 0), ← mk_zero, mk_eq_mk, isConjRoot_zero_iff_eq_zero]
/-
**ConjRootClass.** 是 Mathlib 中的一个实例，位于命名空间 `ConjRootClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Normal K L] [DecidableEq L] [Fintype Gal(L/K)] : DecidableEq (ConjRootClass K L) :=
  Quotient.decidableEq (d := IsConjRoot.decidable)

/-- `c.carrier` is the set of conjugates represented by `c`. -/
/-
**ConjRootClass.carrier** 是 Mathlib 中的一个定义，位于命名空间 `ConjRootClass`。
形式化陈述：carrier (c : ConjRootClass K L) : Set L
参数：c : ConjRootClass K L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`c.carrier` is the set of conjugates represented by `c`.
-/
def carrier (c : ConjRootClass K L) : Set L :=
  mk K ⁻¹' {c}

@[simp]
/-
**ConjRootClass.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：mem_carrier {x : L} {c : ConjRootClass K L} : x in c.carrier ↔ mk K x = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {x : L} {c : ConjRootClass K L} : x ∈ c.carrier ↔ mk K x = c :=
  Iff.rfl

@[simp]
/-
**ConjRootClass.carrier_zero** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：carrier_zero : (0 : ConjRootClass K L).carrier = {0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjRootClass.mem_carrier`：mem_carrier {x : L} {c : ConjRootClass K L} :
 x in c.carrier ↔ mk K x = c
· 使用定理 `ConjRootClass.mk_eq_zero_iff`：mk_eq_zero_iff (x : L) : mk K x = 0 ↔ x = 
0
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem carrier_zero : (0 : ConjRootClass K L).carrier = {0} := by
  ext; rw [mem_carrier, mk_eq_zero_iff, Set.mem_singleton_iff]
/-
**ConjRootClass.carrier_inj** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：carrier_inj : Function.Injective (carrier (K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConjRootClass.ind`：ind {motive : ConjRootClass K L -> Prop} (h : forall 
x : L, motive (mk K x)) (c : ConjRootClass K L) : motive c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem carrier_inj : Function.Injective (carrier (K := K) (L := L)) := by
  intro x y H
  induction x with | h x => ?_
  induction y with | h y => ?_
  simp_rw [Set.ext_iff, mem_carrier] at H
  rw [← H]
/-
**ConjRootClass.** 是 Mathlib 中的一个实例，位于命名空间 `ConjRootClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (ConjRootClass K L) where
  neg := Quotient.map (fun x ↦ -x) (fun _ _ ↦ IsConjRoot.neg)
/-
**ConjRootClass.mk_neg** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：mk_neg (x : L) : - mk K x = mk K (-x)
参数：x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_neg (x : L) : - mk K x = mk K (-x) :=
  rfl
/-
**ConjRootClass.** 是 Mathlib 中的一个实例，位于命名空间 `ConjRootClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InvolutiveNeg (ConjRootClass K L) where
  neg_neg c := by induction c; rw [mk_neg, mk_neg, neg_neg]

@[simp]
/-
**ConjRootClass.carrier_neg** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：carrier_neg (c : ConjRootClass K L) : carrier (-c) = - carrier c
参数：c : ConjRootClass K L。
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
theorem carrier_neg (c : ConjRootClass K L) : carrier (-c) = - carrier c := by
  ext
  simp [mem_carrier, ← mk_neg, neg_eq_iff_eq_neg]
/-
**ConjRootClass.exists_mem_carrier_add_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ConjRo
otClass`。
形式化陈述：exists_mem_carrier_add_eq_zero (x y : ConjRootClass K L) : (existsᵉ (a in 
x.carrier) (b in y.carrier), a + b = 0) ↔ x = -y
参数：x y : ConjRootClass K L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ConjRootClass.mk_neg`：mk_neg (x : L) : - mk K x = mk K (-x)
· 使用定理 `ConjRootClass.mk_eq_mk`：mk_eq_mk {x y : L} : mk K x = mk K y ↔ IsConjRoo
t K x y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `IsConjRoot.refl`：∀ {R : Type u_1} {A : Type u_5} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] {x : A}, IsConjRoot R x x
· 使用引理 `ConjRootClass.ind`：ind {motive : ConjRootClass K L -> Prop} (h : forall 
x : L, motive (mk K x)) (c : ConjRootClass K L) : motive c
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_mem_carrier_add_eq_zero (x y : ConjRootClass K L) :
    (∃ᵉ (a ∈ x.carrier) (b ∈ y.carrier), a + b = 0) ↔ x = -y := by
  simp_rw [mem_carrier]
  constructor
  · rintro ⟨a, rfl, b, rfl, h⟩
    rw [mk_neg, mk_eq_mk, add_eq_zero_iff_eq_neg.mp h]
  · rintro rfl
    induction y with
    | h y => exact ⟨-y, mk_neg y, y, rfl, neg_add_cancel _⟩
/-
**ConjRootClass.** 是 Mathlib 中的一个实例，位于命名空间 `ConjRootClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Normal K L] [DecidableEq L] [Fintype Gal(L/K)] (c : ConjRootClass K L) :
    DecidablePred (· ∈ c.carrier) := fun x ↦
  decidable_of_iff (mk K x = c) (by simp)
/-
**ConjRootClass.** 是 Mathlib 中的一个实例，位于命名空间 `ConjRootClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Normal K L] [DecidableEq L] [Fintype Gal(L/K)] (c : ConjRootClass K L) :
    Fintype c.carrier :=
  Quotient.recOnSubsingleton c fun x =>
    .ofFinset
      ((Finset.univ (α := Gal(L/K))).image (· x))
      (fun _ ↦ by simp [← isConjRoot_iff_exists_algEquiv, ← mk_eq_mk])

open Polynomial

/-- `c.minpoly` is the minimal polynomial of the conjugates. -/
/-
**ConjRootClass.minpoly** 是 Mathlib 中的一个定义，位于命名空间 `ConjRootClass`。
形式化陈述：{K : Type u_1} →   {L : Type u_2} → [inst : Field K] → [inst_1 : Field L] 
→ [inst_2 : Algebra K L] → ConjRootClass K L → Polynomial K
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`c.minpoly` is the minimal polynomial of the conjugates.
-/
protected noncomputable def minpoly : ConjRootClass K L → K[X] :=
  Quotient.lift (minpoly K) fun _ _ ↦ id

@[simp]
/-
**ConjRootClass.minpoly_mk** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：minpoly_mk (x : L) : (mk K x).minpoly = minpoly K x
参数：x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem minpoly_mk (x : L) : (mk K x).minpoly = minpoly K x :=
  rfl

@[simp]
/-
**ConjRootClass.minpoly_inj** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：minpoly_inj {c d : ConjRootClass K L} : c.minpoly = d.minpoly ↔ c = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConjRootClass.ind`：ind {motive : ConjRootClass K L -> Prop} (h : forall 
x : L, motive (mk K x)) (c : ConjRootClass K L) : motive c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem minpoly_inj {c d : ConjRootClass K L} : c.minpoly = d.minpoly ↔ c = d := by
  induction c
  induction d
  simp [isConjRoot_def]
/-
**ConjRootClass.minpoly_injective** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：minpoly_injective : Function.Injective (ConjRootClass.minpoly (K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ConjRootClass.minpoly_inj`：minpoly_inj {c d : ConjRootClass K L} : c.min
poly = d.minpoly ↔ c = d
-/
theorem minpoly_injective : Function.Injective (ConjRootClass.minpoly (K := K) (L := L)) :=
  fun _ _ ↦ minpoly_inj.mp
/-
**ConjRootClass.splits_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：splits_minpoly [n : Normal K L] (c : ConjRootClass K L) : Splits (c.minpol
y.map (algebraMap K L))
参数：c : ConjRootClass K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConjRootClass.ind`：ind {motive : ConjRootClass K L -> Prop} (h : forall 
x : L, motive (mk K x)) (c : ConjRootClass K L) : motive c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjRootClass.minpoly_mk`：minpoly_mk (x : L) : (mk K x).minpoly = minpol
y K x
· 使用定理 `Normal.splits`：Normal.splits (_ : Normal F K) (x : K) : Splits ((minpoly
 F x).map (algebraMap F K))
-/
theorem splits_minpoly [n : Normal K L] (c : ConjRootClass K L) :
    Splits (c.minpoly.map (algebraMap K L)) := by
  induction c
  rw [minpoly_mk]
  exact n.splits _

section IsAlgebraic

variable [Algebra.IsAlgebraic K L]

/-
**ConjRootClass.monic_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：monic_minpoly (c : ConjRootClass K L) : c.minpoly.Monic
参数：c : ConjRootClass K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConjRootClass.ind`：ind {motive : ConjRootClass K L -> Prop} (h : forall 
x : L, motive (mk K x)) (c : ConjRootClass K L) : motive c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjRootClass.minpoly_mk`：minpoly_mk (x : L) : (mk K x).minpoly = minpol
y K x
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
-/
theorem monic_minpoly (c : ConjRootClass K L) : c.minpoly.Monic := by
  induction c
  rw [minpoly_mk]
  exact minpoly.monic (Algebra.IsIntegral.isIntegral _)
/-
**ConjRootClass.minpoly_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：minpoly_ne_zero (c : ConjRootClass K L) : c.minpoly != 0
参数：c : ConjRootClass K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ConjRootClass.monic_minpoly`：monic_minpoly (c : ConjRootClass K L) : c.m
inpoly.Monic
-/
theorem minpoly_ne_zero (c : ConjRootClass K L) : c.minpoly ≠ 0 :=
  c.monic_minpoly.ne_zero
/-
**ConjRootClass.irreducible_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：irreducible_minpoly (c : ConjRootClass K L) : Irreducible c.minpoly
参数：c : ConjRootClass K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConjRootClass.ind`：ind {motive : ConjRootClass K L -> Prop} (h : forall 
x : L, motive (mk K x)) (c : ConjRootClass K L) : motive c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjRootClass.minpoly_mk`：minpoly_mk (x : L) : (mk K x).minpoly = minpol
y K x
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
-/
theorem irreducible_minpoly (c : ConjRootClass K L) : Irreducible c.minpoly := by
  induction c
  rw [minpoly_mk]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
/-
**ConjRootClass.aeval_minpoly_iff** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：aeval_minpoly_iff (x : L) (c : ConjRootClass K L) : aeval x c.minpoly = 0 
↔ mk K x = c
参数：x : L；c : ConjRootClass K L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConjRootClass.ind`：ind {motive : ConjRootClass K L -> Prop} (h : forall 
x : L, motive (mk K x)) (c : ConjRootClass K L) : motive c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isConjRoot_iff_aeval_eq_zero`：isConjRoot_iff_aeval_eq_zero [IsDomain A] 
{x y : A} (h : IsIntegral K x) : IsConjRoot K x y ↔ aeval y (minpoly K x) = 0
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `comm`：comm [Std.Symm r] {a b : α} : r a b ↔ r b a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `IsConjRoot.instIsEquiv`：∀ {R : Type u_1} {A : Type u_5} [inst : CommRing
 R] [inst_1 : Ring A] [inst_2 : Algebra R A], IsEquiv A (IsConjRoot R)
-/
theorem aeval_minpoly_iff (x : L) (c : ConjRootClass K L) :
    aeval x c.minpoly = 0 ↔ mk K x = c := by
  induction c
  simpa [← isConjRoot_iff_aeval_eq_zero (Algebra.IsIntegral.isIntegral _)] using comm
/-
**ConjRootClass.rootSet_minpoly_eq_carrier** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootCl
ass`。
形式化陈述：rootSet_minpoly_eq_carrier (c : ConjRootClass K L) : c.minpoly.rootSet L =
 c.carrier
参数：c : ConjRootClass K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjRootClass.mem_carrier`：mem_carrier {x : L} {c : ConjRootClass K L} :
 x in c.carrier ↔ mk K x = c
· 使用定理 `Polynomial.mem_rootSet`：mem_rootSet {p : T[X]} {S : Type*} [IsDomain T] 
[CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] {a : S} : a i
n p.rootSet …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `ConjRootClass.aeval_minpoly_iff`：aeval_minpoly_iff (x : L) (c : ConjRoot
Class K L) : aeval x c.minpoly = 0 ↔ mk K x = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ConjRootClass.minpoly_ne_zero`：minpoly_ne_zero (c : ConjRootClass K L) :
 c.minpoly != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rootSet_minpoly_eq_carrier (c : ConjRootClass K L) :
    c.minpoly.rootSet L = c.carrier := by
  ext x
  rw [mem_carrier, mem_rootSet, aeval_minpoly_iff x c]
  simp [c.minpoly_ne_zero]

end IsAlgebraic

section IsSeparable

variable [Algebra.IsSeparable K L]

/-
**ConjRootClass.separable_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：separable_minpoly (c : ConjRootClass K L) : Separable c.minpoly
参数：c : ConjRootClass K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConjRootClass.ind`：ind {motive : ConjRootClass K L -> Prop} (h : forall 
x : L, motive (mk K x)) (c : ConjRootClass K L) : motive c
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
-/
theorem separable_minpoly (c : ConjRootClass K L) : Separable c.minpoly := by
  induction c
  exact Algebra.IsSeparable.isSeparable K _
/-
**ConjRootClass.nodup_aroots_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass`。
形式化陈述：nodup_aroots_minpoly (c : ConjRootClass K L) : (c.minpoly.aroots L).Nodup
参数：c : ConjRootClass K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.nodup_roots`：nodup_roots {p : R[X]} (hsep : Separable p) : p.
roots.Nodup
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.Separable.map`：∀ {R : Type u} [inst : CommSemiring R] {S : Ty
pe v} [inst_1 : CommSemiring S] {p : Polynomial R},   p.Separable → ∀ {f : R →+*
 S}, (Polynomi…
· 使用定理 `ConjRootClass.separable_minpoly`：separable_minpoly (c : ConjRootClass K 
L) : Separable c.minpoly
-/
theorem nodup_aroots_minpoly (c : ConjRootClass K L) : (c.minpoly.aroots L).Nodup :=
  nodup_roots c.separable_minpoly.map
/-
**ConjRootClass.aroots_minpoly_eq_carrier_val** 是 Mathlib 中的一个定理，位于命名空间 `ConjRoo
tClass`。
形式化陈述：aroots_minpoly_eq_carrier_val (c : ConjRootClass K L) [Fintype c.carrier] 
: c.minpoly.aroots L = c.carrier.toFinset.1
参数：c : ConjRootClass K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.rootSet_def`：rootSet_def (p : T[X]) (S) [CommRing S] [IsDomai
n S] [Algebra T S] [DecidableEq S] : p.rootSet S = (p.aroots S).toFinset
· 使用定理 `Finset.toFinset_coe`：Finset.toFinset_coe (s : Finset α) [Fintype (s : Se
t α)] : (s : Set α).toFinset = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
· 使用定理 `ConjRootClass.nodup_aroots_minpoly`：nodup_aroots_minpoly (c : ConjRootCl
ass K L) : (c.minpoly.aroots L).Nodup
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aroots_minpoly_eq_carrier_val (c : ConjRootClass K L) [Fintype c.carrier] :
    c.minpoly.aroots L = c.carrier.toFinset.1 := by
  classical
  simp_rw [← rootSet_minpoly_eq_carrier, rootSet_def, Finset.toFinset_coe, Multiset.toFinset_val,
    c.nodup_aroots_minpoly.dedup]
/-
**ConjRootClass.carrier_eq_mk_aroots_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `ConjRoot
Class`。
形式化陈述：carrier_eq_mk_aroots_minpoly (c : ConjRootClass K L) [Fintype c.carrier] :
 c.carrier.toFinset = ⟨c.minpoly.aroots L, c.nodup_aroots_minpoly⟩
参数：c : ConjRootClass K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `ConjRootClass.nodup_aroots_minpoly`：nodup_aroots_minpoly (c : ConjRootCl
ass K L) : (c.minpoly.aroots L).Nodup
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ConjRootClass.aroots_minpoly_eq_carrier_val`：aroots_minpoly_eq_carrier_v
al (c : ConjRootClass K L) [Fintype c.carrier] : c.minpoly.aroots L = c.carrier.
toFinset.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mk.congr_simp`：∀ {α : Type u_4} (val val_1 : Multiset α) (e_val :
 val = val_1) (nodup : val.Nodup),   { val := val, nodup := nodup } = { val := v
al_1, nodu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem carrier_eq_mk_aroots_minpoly (c : ConjRootClass K L) [Fintype c.carrier] :
    c.carrier.toFinset = ⟨c.minpoly.aroots L, c.nodup_aroots_minpoly⟩ := by
  simp only [aroots_minpoly_eq_carrier_val]
/-
**ConjRootClass.minpoly.map_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `ConjRootClass.min
poly`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] [Algebra.IsSeparable K L]   [Normal K L] (c : ConjRootClass K L
) [inst_5 : Fintype ↑c.carrier],   Polynomial.map (algebraMap K L) c.minpoly = ∏
 x ∈ c.carrier.toFinset, (Polynomial.X - Polynomial.C x)
参数：c : ConjRootClass K L；algebraMap K L；Polynomial.X - Polynomial.C x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.rootSet_def`：rootSet_def (p : T[X]) (S) [CommRing S] [IsDomai
n S] [Algebra T S] [DecidableEq S] : p.rootSet S = (p.aroots S).toFinset
· 使用定理 `Finset.toFinset_coe`：Finset.toFinset_coe (s : Finset α) [Fintype (s : Se
t α)] : (s : Set α).toFinset = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dedup_eq_self`：dedup_eq_self {s : Multiset α} : dedup s = s ↔ N
odup s
· 使用定理 `Polynomial.nodup_roots`：nodup_roots {p : R[X]} (hsep : Separable p) : p.
roots.Nodup
· 使用定理 `Polynomial.Separable.map`：∀ {R : Type u} [inst : CommSemiring R] {S : Ty
pe v} [inst_1 : CommSemiring S] {p : Polynomial R},   p.Separable → ∀ {f : R →+*
 S}, (Polynomi…
· 使用定理 `ConjRootClass.separable_minpoly`：separable_minpoly (c : ConjRootClass K 
L) : Separable c.minpoly
· 使用定理 `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq`：prod_multise
t_X_sub_C_of_monic_of_roots_card_eq (hp : p.Monic) (hroots : Multiset.card p.roo
ts = p.natDegree) : (p.roots.map fun a => X - C …
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `ConjRootClass.monic_minpoly`：monic_minpoly (c : ConjRootClass K L) : c.m
inpoly.Monic
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.splits_iff_card_roots`：splits_iff_card_roots : Splits f ↔ f.r
oots.card = f.natDegree
· 使用定理 `ConjRootClass.splits_minpoly`：splits_minpoly [n : Normal K L] (c : ConjR
ootClass K L) : Splits (c.minpoly.map (algebraMap K L))
-/
theorem minpoly.map_eq_prod [Normal K L] (c : ConjRootClass K L) [Fintype c.carrier] :
    c.minpoly.map (algebraMap K L) = ∏ x ∈ c.carrier.toFinset, (X - C x) := by
  classical
  simp_rw [← rootSet_minpoly_eq_carrier, Finset.prod_eq_multiset_prod, rootSet_def,
    Finset.toFinset_coe, Multiset.toFinset_val]
  rw [Multiset.dedup_eq_self.mpr (nodup_roots c.separable_minpoly.map),
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (c.monic_minpoly.map _)]
  rw [← splits_iff_card_roots]
  exact c.splits_minpoly

end IsSeparable

end ConjRootClass

