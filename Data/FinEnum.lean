/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Data.List.Pi

/-!
Type class for finitely enumerable types. The property is stronger
than `Fintype` in that it assigns each element a rank in a finite
enumeration.
-/

@[expose] public section


universe u v

open Finset

/-- `FinEnum α` means that `α` is finite and can be enumerated in some order,
  i.e. `α` has an explicit bijection with `Fin n` for some n. -/
/-
**FinEnum** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Sort u_1 → Sort (max 1 u_1)
参数：max 1 u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FinEnum α` means that `α` is finite and can be enumerated in some order,
  i.e. `α` has an explicit bijection with `Fin n` for some n.
-/
class FinEnum (α : Sort*) where
  /-- `FinEnum.card` is the cardinality of the `FinEnum` -/
  card : ℕ
  /-- `FinEnum.Equiv` states that type `α` is in bijection with `Fin card`,
  the size of the `FinEnum` -/
  equiv : α ≃ Fin card
  [decEq : DecidableEq α]

attribute [instance_reducible, instance 100] FinEnum.decEq

namespace FinEnum

variable {α : Type u} {β : α → Type v}

/-- transport a `FinEnum` instance across an equivalence -/
@[instance_reducible]
/-
**FinEnum.ofEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum`。
形式化陈述：ofEquiv (α) {β} [FinEnum α] (h : β ≃ α) : FinEnum β where card
参数：α；h : β ≃ α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
transport a `FinEnum` instance across an equivalence
-/
def ofEquiv (α) {β} [FinEnum α] (h : β ≃ α) : FinEnum β where
  card := card α
  equiv := h.trans (equiv)
  decEq := (h.trans (equiv)).decidableEq

/-- create a `FinEnum` instance from an exhaustive list without duplicates -/
@[instance_reducible]
/-
**FinEnum.ofNodupList** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum`。
形式化陈述：ofNodupList [DecidableEq α] (xs : List α) (h : forall x : α, x in xs) (h' 
: List.Nodup xs) : FinEnum α where card
参数：xs : List α；h : forall x : α, x in xs；h' : List.Nodup xs。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
create a `FinEnum` instance from an exhaustive list without duplicates
-/
def ofNodupList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) (h' : List.Nodup xs) :
    FinEnum α where
  card := xs.length
  equiv :=
    ⟨fun x => ⟨xs.idxOf x, by rw [List.idxOf_lt_length_iff]; apply h⟩, xs.get, fun x => by simp,
      fun i => by ext; simp [h'.idxOf_getElem]⟩

/-- create a `FinEnum` instance from an exhaustive list; duplicates are removed -/
@[instance_reducible]
/-
**FinEnum.ofList** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum`。
形式化陈述：ofList [DecidableEq α] (xs : List α) (h : forall x : α, x in xs) : FinEnum
 α
参数：xs : List α；h : forall x : α, x in xs。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.nodup_dedup`：nodup_dedup : forall l : List α, Nodup (dedup l)

--- 原说明 ---
create a `FinEnum` instance from an exhaustive list; duplicates are removed
-/
def ofList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) : FinEnum α :=
  ofNodupList xs.dedup (by simp [*]) (List.nodup_dedup _)
/-
**FinEnum.card_ofList** 是 Mathlib 中的一个引理，位于命名空间 `FinEnum`。
形式化陈述：card_ofList [DecidableEq α] (xs : List α) (h : forall x : α, x in xs) : (F
inEnum.ofList xs h).card = xs.dedup.length
参数：xs : List α；h : forall x : α, x in xs。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma card_ofList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) :
    (FinEnum.ofList xs h).card = xs.dedup.length := rfl

/-- create an exhaustive list of the values of a given type -/
/-
**FinEnum.toList** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum`。
形式化陈述：toList (α) [FinEnum α] : List α
参数：α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
create an exhaustive list of the values of a given type
-/
def toList (α) [FinEnum α] : List α :=
  (List.finRange (card α)).map equiv.symm

open Function

@[simp]
/-
**FinEnum.mem_toList** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：mem_toList [FinEnum α] (x : α) : x in toList α
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_toList [FinEnum α] (x : α) : x ∈ toList α := by
  simp only [toList, List.mem_map, List.mem_finRange, true_and]; exists equiv x; simp

@[simp]
/-
**FinEnum.nodup_toList** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：nodup_toList [FinEnum α] : List.Nodup (toList α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.map`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β}, Fu
nction.Injective f → l.Nodup → (List.map f l).Nodup
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `List.nodup_finRange`：∀ (n : ℕ), (List.finRange n).Nodup
-/
theorem nodup_toList [FinEnum α] : List.Nodup (toList α) := by
  simp only [toList]; apply List.Nodup.map <;> [apply Equiv.injective; apply List.nodup_finRange]

/-- create a `FinEnum` instance using a surjection -/
@[instance_reducible]
/-
**FinEnum.ofSurjective** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum`。
形式化陈述：ofSurjective {β} (f : β -> α) [DecidableEq α] [FinEnum β] (h : Surjective 
f) : FinEnum α
参数：f : β -> α；h : Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
create a `FinEnum` instance using a surjection
-/
def ofSurjective {β} (f : β → α) [DecidableEq α] [FinEnum β] (h : Surjective f) : FinEnum α :=
  ofList ((toList β).map f) (by intro; simpa using h _)

/-- create a `FinEnum` instance using an injection -/
@[instance_reducible]
/-
**FinEnum.ofInjective** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum`。
形式化陈述：ofInjective {α β} (f : α -> β) [DecidableEq α] [FinEnum β] (h : Injective 
f) : FinEnum α
参数：f : α -> β；h : Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
create a `FinEnum` instance using an injection
-/
noncomputable def ofInjective {α β} (f : α → β) [DecidableEq α] [FinEnum β] (h : Injective f) :
    FinEnum α :=
  ofList ((toList β).filterMap (partialInv f))
    (by
      intro x
      simp only [mem_toList, true_and, List.mem_filterMap]
      use f x
      simp only [h, Function.partialInv_left])
/-
**FinEnum._root_.ULift.instFinEnum** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.ULift.instFinEnum [FinEnum α] : FinEnum (ULift α) :=
  ⟨card α, Equiv.ulift.trans equiv⟩

@[simp]
/-
**FinEnum.card_ulift** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：card_ulift [FinEnum (ULift α)] [FinEnum α] : card (ULift α) = card α
参数：ULift α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Fin.equiv_iff_eq`：equiv_iff_eq : Nonempty (Fin m ≃ Fin n) ↔ m = n
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem card_ulift [FinEnum (ULift α)] [FinEnum α] : card (ULift α) = card α :=
  Fin.equiv_iff_eq.mp ⟨equiv.symm.trans Equiv.ulift |>.trans equiv⟩

section ULift
variable [FinEnum α] (a : α) (a' : ULift α) (i : Fin (card α))

/-
**FinEnum.equiv_up** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：∀ {α : Type u} [inst : FinEnum α] (a : α), FinEnum.equiv { down := a } = F
inEnum.equiv a
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma equiv_up : equiv (ULift.up a) = equiv a := rfl
/-
**FinEnum.equiv_down** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：∀ {α : Type u} [inst : FinEnum α] (a' : ULift.{u_1, u} α), FinEnum.equiv a
'.down = FinEnum.equiv a'
参数：a' : ULift.{u_1, u} α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma equiv_down : equiv a'.down = equiv a' := rfl
/-
**FinEnum.up_equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：∀ {α : Type u} [inst : FinEnum α] (i : Fin (FinEnum.card α)), { down := Fi
nEnum.equiv.symm i } = FinEnum.equiv.symm i
参数：i : Fin (FinEnum.card α)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma up_equiv_symm : ULift.up (equiv.symm i) = (equiv (α := ULift α)).symm i := rfl
/-
**FinEnum.down_equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：∀ {α : Type u} [inst : FinEnum α] (i : Fin (FinEnum.card α)), (FinEnum.equ
iv.symm i).down = FinEnum.equiv.symm i
参数：i : Fin (FinEnum.card α)；FinEnum.equiv.symm i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma down_equiv_symm : ((equiv (α := ULift α)).symm i).down = equiv.symm i := rfl

end ULift

/-
**FinEnum.pempty** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
形式化陈述：pempty : FinEnum PEmpty
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pempty : FinEnum PEmpty :=
  ofList [] fun x => PEmpty.elim x
/-
**FinEnum.card_pempty** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：FinEnum.card PEmpty.{u_1 + 1} = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma card_pempty : FinEnum.card PEmpty = 0 := rfl
/-
**FinEnum.empty** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
形式化陈述：empty : FinEnum Empty
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance empty : FinEnum Empty :=
  ofList [] fun x => Empty.elim x
/-
**FinEnum.card_empty** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：FinEnum.card Empty = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma card_empty : FinEnum.card Empty = 0 := rfl
/-
**FinEnum.punit** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
形式化陈述：punit : FinEnum PUnit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance punit : FinEnum PUnit :=
  ofList [PUnit.unit] fun x => by simp
/-
**FinEnum.card_punit** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：FinEnum.card PUnit.{u_1 + 1} = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma card_punit : FinEnum.card PUnit = 1 := rfl
/-
**FinEnum.prod** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
形式化陈述：prod {β} [FinEnum α] [FinEnum β] : FinEnum (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance prod {β} [FinEnum α] [FinEnum β] : FinEnum (α × β) :=
  ofList (toList α ×ˢ toList β) fun x => by cases x; simp
/-
**FinEnum.sum** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
形式化陈述：sum {β} [FinEnum α] [FinEnum β] : FinEnum (α oplus β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sum {β} [FinEnum α] [FinEnum β] : FinEnum (α ⊕ β) :=
  ofList ((toList α).map Sum.inl ++ (toList β).map Sum.inr) fun x => by cases x <;> simp
/-
**FinEnum.fin** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
形式化陈述：fin {n} : FinEnum (Fin n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fin {n} : FinEnum (Fin n) :=
  ofList (List.finRange _) (by simp)

@[simp]
/-
**FinEnum.card_fin** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：card_fin {n} [FinEnum (Fin n)] : card (Fin n) = n
参数：Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Fin.equiv_iff_eq`：equiv_iff_eq : Nonempty (Fin m ≃ Fin n) ↔ m = n
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem card_fin {n} [FinEnum (Fin n)] : card (Fin n) = n := Fin.equiv_iff_eq.mp ⟨equiv.symm⟩
/-
**FinEnum.Quotient.enum** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum.Quotient`。
形式化陈述：{α : Type u} → [FinEnum α] → (s : Setoid α) → [DecidableRel fun x1 x2 => x
1 ≈ x2] → FinEnum (Quotient s)
参数：s : Setoid α；Quotient s。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
instance Quotient.enum [FinEnum α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α → α → Prop)] :
    FinEnum (Quotient s) :=
  FinEnum.ofSurjective Quotient.mk'' fun x => Quotient.inductionOn x fun x => ⟨x, rfl⟩

/-- enumerate all finite sets of a given type -/
/-
**FinEnum.Finset.enum** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum.Finset`。
形式化陈述：{α : Type u} → [DecidableEq α] → List α → List (Finset α)
参数：Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
enumerate all finite sets of a given type
-/
def Finset.enum [DecidableEq α] : List α → List (Finset α)
  | [] => [∅]
  | x :: xs => do
    let r ← Finset.enum xs
    [r, insert x r]

@[simp, grind =]
/-
**FinEnum.Finset.mem_enum** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum.Finset`。
形式化陈述：∀ {α : Type u} [inst : DecidableEq α] (s : Finset α) (xs : List α), s ∈ Fi
nEnum.Finset.enum xs ↔ ∀ x ∈ s, x ∈ xs
参数：s : Finset α；xs : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem Finset.mem_enum [DecidableEq α] (s : Finset α) (xs : List α) :
    s ∈ Finset.enum xs ↔ ∀ x ∈ s, x ∈ xs := by
  induction xs generalizing s with
  | nil => simp [enum, eq_empty_iff_forall_notMem]
  | cons x xs ih =>
      simp only [enum, List.bind_eq_flatMap, List.mem_flatMap, List.mem_cons,
        List.not_mem_nil, or_false, ih]
      refine ⟨by aesop, fun hs => ⟨s.erase x, ?_⟩⟩
      simp only [or_iff_not_imp_left] at hs
      simp +contextual [eq_comm (a := s), or_iff_not_imp_left, hs]
/-
**FinEnum.Finset.finEnum** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum.Finset`。
形式化陈述：{α : Type u} → [FinEnum α] → FinEnum (Finset α)
参数：Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Finset.finEnum [FinEnum α] : FinEnum (Finset α) :=
  ofList (Finset.enum (toList α)) (by simp)
/-
**FinEnum.Subtype.finEnum** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum.Subtype`。
形式化陈述：{α : Type u} → [FinEnum α] → (p : α → Prop) → [DecidablePred p] → FinEnum 
{ x // p x }
参数：p : α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.finEnum [FinEnum α] (p : α → Prop) [DecidablePred p] : FinEnum { x // p x } :=
  ofList ((toList α).filterMap fun x => if h : p x then some ⟨_, h⟩ else none)
    (by rintro ⟨x, h⟩; simpa)
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (β : α → Type v) [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Sigma β) :=
  ofList ((toList α).flatMap fun a => (toList (β a)).map <| Sigma.mk a)
    (by intro x; cases x; simp)
/-
**FinEnum.PSigma.finEnum** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum.PSigma`。
形式化陈述：{α : Type u} → {β : α → Type v} → [FinEnum α] → [(a : α) → FinEnum (β a)] 
→ FinEnum ((a : α) ×' β a)
参数：a : α；β a；(a : α) ×' β a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PSigma.finEnum [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Σ' a, β a) :=
  FinEnum.ofEquiv _ (Equiv.psigmaEquivSigma _)
/-
**FinEnum.PSigma.finEnumPropLeft** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum.PSigma`。
形式化陈述：{α : Prop} → {β : α → Type v} → [(a : α) → FinEnum (β a)] → [Decidable α] 
→ FinEnum ((a : α) ×' β a)
参数：a : α；β a；(a : α) ×' β a。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p
-/
instance PSigma.finEnumPropLeft {α : Prop} {β : α → Type v} [∀ a, FinEnum (β a)] [Decidable α] :
    FinEnum (Σ' a, β a) :=
  if h : α then ofList ((toList (β h)).map <| PSigma.mk h) fun ⟨a, Ba⟩ => by simp
  else ofList [] fun ⟨a, _⟩ => (h a).elim
/-
**FinEnum.PSigma.finEnumPropRight** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum.PSigma`。
形式化陈述：{α : Type u} → {β : α → Prop} → [FinEnum α] → [(a : α) → Decidable (β a)] 
→ FinEnum ((a : α) ×' β a)
参数：a : α；β a；(a : α) ×' β a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PSigma.finEnumPropRight {β : α → Prop} [FinEnum α] [∀ a, Decidable (β a)] :
    FinEnum (Σ' a, β a) :=
  FinEnum.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
/-
**FinEnum.PSigma.finEnumPropProp** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum.PSigma`。
形式化陈述：{α : Prop} → {β : α → Prop} → [Decidable α] → [(a : α) → Decidable (β a)] 
→ FinEnum ((a : α) ×' β a)
参数：a : α；β a；(a : α) ×' β a。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p
-/
instance PSigma.finEnumPropProp {α : Prop} {β : α → Prop} [Decidable α] [∀ a, Decidable (β a)] :
    FinEnum (Σ' a, β a) :=
  if h : ∃ a, β a then ofList [⟨h.fst, h.snd⟩] (by simp)
  else ofList [] fun a => (h ⟨a.fst, a.snd⟩).elim
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] (xs : List α) : FinEnum { x : α // x ∈ xs } := ofList xs.attach (by simp)
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [FinEnum α] : Fintype α where
  elems := univ.map equiv.symm.toEmbedding
  complete := by intros; simp

/-- The enumeration merely adds an ordering, leaving the cardinality as is. -/
/-
**FinEnum.card_eq_fintypeCard** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：card_eq_fintypeCard {α : Type u} [FinEnum α] [Fintype α] : card α = Fintyp
e.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Fin.equiv_iff_eq`：equiv_iff_eq : Nonempty (Fin m ≃ Fin n) ↔ m = n
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The enumeration merely adds an ordering, leaving the cardinality as is.
-/
theorem card_eq_fintypeCard {α : Type u} [FinEnum α] [Fintype α] : card α = Fintype.card α :=
  Fintype.truncEquivFin α |>.inductionOn (fun h ↦ Fin.equiv_iff_eq.mp ⟨equiv.symm.trans h⟩)

/-- Any two enumerations of the same type have the same length. -/
/-
**FinEnum.card_unique** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：card_unique {α : Type u} (e₁ e₂ : FinEnum α) : e₁.card = e₂.card
参数：e₁ e₂ : FinEnum α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FinEnum.card_eq_fintypeCard`：card_eq_fintypeCard {α : Type u} [FinEnum α
] [Fintype α] : card α = Fintype.card α
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Any two enumerations of the same type have the same length.
-/
theorem card_unique {α : Type u} (e₁ e₂ : FinEnum α) : e₁.card = e₂.card :=
  calc _
  _ = _ := @card_eq_fintypeCard _ e₁ inferInstance
  _ = _ := Fintype.card_congr' rfl
  _ = _ := @card_eq_fintypeCard _ e₂ inferInstance |>.symm

/-- A type indexable by `Fin 0` is empty and vice versa. -/
/-
**FinEnum.card_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：card_eq_zero_iff {α : Type u} [FinEnum α] : card α = 0 ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Eq.congr_left`：∀ {α : Sort u_1} {x y z : α}, x = y → (x = z ↔ y = z)
· 使用定理 `FinEnum.card_eq_fintypeCard`：card_eq_fintypeCard {α : Type u} [FinEnum α
] [Fintype α] : card α = Fintype.card α
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α

--- 原说明 ---
A type indexable by `Fin 0` is empty and vice versa.
-/
theorem card_eq_zero_iff {α : Type u} [FinEnum α] : card α = 0 ↔ IsEmpty α :=
  Eq.congr_left card_eq_fintypeCard |>.trans Fintype.card_eq_zero_iff

/-- Any enumeration of an empty type has length 0. -/
/-
**FinEnum.card_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：card_eq_zero {α : Type u} [FinEnum α] [IsEmpty α] : card α = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FinEnum.card_eq_zero_iff`：card_eq_zero_iff {α : Type u} [FinEnum α] : ca
rd α = 0 ↔ IsEmpty α

--- 原说明 ---
Any enumeration of an empty type has length 0.
-/
theorem card_eq_zero {α : Type u} [FinEnum α] [IsEmpty α] : card α = 0 :=
  card_eq_zero_iff.mpr ‹_›

/-- A type indexable by `Fin n` with positive `n` is inhabited and vice versa. -/
/-
**FinEnum.card_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：card_pos_iff {α : Type u} [FinEnum α] : 0 < card α ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FinEnum.card_eq_fintypeCard`：card_eq_fintypeCard {α : Type u} [FinEnum α
] [Fintype α] : card α = Fintype.card α

--- 原说明 ---
A type indexable by `Fin n` with positive `n` is inhabited and vice versa.
-/
theorem card_pos_iff {α : Type u} [FinEnum α] : 0 < card α ↔ Nonempty α :=
  card_eq_fintypeCard (α := α) ▸ Fintype.card_pos_iff

/-- Any non-empty enumeration has more than one element. -/
/-
**FinEnum.card_pos** 是 Mathlib 中的一个引理，位于命名空间 `FinEnum`。
形式化陈述：card_pos {α : Type*} [FinEnum α] [Nonempty α] : 0 < card α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FinEnum.card_pos_iff`：card_pos_iff {α : Type u} [FinEnum α] : 0 < card α
 ↔ Nonempty α

--- 原说明 ---
Any non-empty enumeration has more than one element.
-/
lemma card_pos {α : Type*} [FinEnum α] [Nonempty α] : 0 < card α :=
  card_pos_iff.mpr ‹_›

/-- No non-empty enumeration has 0 elements. -/
/-
**FinEnum.card_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `FinEnum`。
形式化陈述：card_ne_zero {α : Type*} [FinEnum α] [Nonempty α] : card α != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `FinEnum.card_pos`：card_pos {α : Type*} [FinEnum α] [Nonempty α] : 0 < ca
rd α

--- 原说明 ---
No non-empty enumeration has 0 elements.
-/
lemma card_ne_zero {α : Type*} [FinEnum α] [Nonempty α] : card α ≠ 0 := card_pos.ne'

/-- Any enumeration of a type with unique inhabitant has length 1. -/
/-
**FinEnum.card_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：card_eq_one (α : Type u) [FinEnum α] [Unique α] : card α = 1
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FinEnum.card_eq_fintypeCard`：card_eq_fintypeCard {α : Type u} [FinEnum α
] [Fintype α] : card α = Fintype.card α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq_one_iff_nonempty_unique`：card_eq_one_iff_nonempty_unique
 : card α = 1 ↔ Nonempty (Unique α)

--- 原说明 ---
Any enumeration of a type with unique inhabitant has length 1.
-/
theorem card_eq_one (α : Type u) [FinEnum α] [Unique α] : card α = 1 :=
  card_eq_fintypeCard.trans <| Fintype.card_eq_one_iff_nonempty_unique.mpr ⟨‹_›⟩
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : Unique (FinEnum α) where
  default := ⟨0, Equiv.equivOfIsEmpty α (Fin 0)⟩
  uniq e := by
    change FinEnum.mk e.1 e.2 = _
    congr 1
    · exact card_eq_zero
    · refine heq_of_cast_eq ?_ (Subsingleton.allEq _ _)
      exact congrArg (α ≃ Fin ·) <| card_eq_zero
    · funext x
      exact ‹IsEmpty α›.elim x

/-- An empty type has a trivial enumeration. Not registered as an instance, to make sure that there
aren't two definitionally differing instances around. -/
@[instance_reducible]
/-
**FinEnum.ofIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum`。
形式化陈述：ofIsEmpty [IsEmpty α] : FinEnum α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An empty type has a trivial enumeration. Not registered as an instance, to make 
sure that there
aren't two definitionally differing instances around.
-/
def ofIsEmpty [IsEmpty α] : FinEnum α := default
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique α] : Unique (FinEnum α) where
  default := ⟨1, Equiv.ofUnique α (Fin 1)⟩
  uniq e := by
    change FinEnum.mk e.1 e.2 = _
    congr 1
    · exact card_eq_one α
    · refine heq_of_cast_eq ?_ (Subsingleton.allEq _ _)
      exact congrArg (α ≃ Fin ·) <| card_eq_one α
    · subsingleton

/-- A type with unique inhabitant has a trivial enumeration. Not registered as an instance, to make
sure that there aren't two definitionally differing instances around. -/
@[instance_reducible]
/-
**FinEnum.ofUnique** 是 Mathlib 中的一个定义，位于命名空间 `FinEnum`。
形式化陈述：ofUnique [Unique α] : FinEnum α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type with unique inhabitant has a trivial enumeration. Not registered as an in
stance, to make
sure that there aren't two definitionally differing instances around.
-/
def ofUnique [Unique α] : FinEnum α := default
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FinEnum UInt8 where
  card := 2 ^ 8
  equiv := ⟨UInt8.toFin, UInt8.ofFin, by intro x; simp, by intro x; simp⟩
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FinEnum UInt16 where
  card := 2 ^ 16
  equiv := ⟨UInt16.toFin, UInt16.ofFin, by intro x; simp, by intro x; simp⟩
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FinEnum UInt32 where
  card := 2 ^ 32
  equiv := ⟨UInt32.toFin, UInt32.ofFin, by intro x; simp, by intro x; simp⟩
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FinEnum UInt64 where
  card := 2 ^ 64
  equiv := ⟨UInt64.toFin, UInt64.ofFin, by intro x; simp, by intro x; simp⟩
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FinEnum Int8 where
  card := 2 ^ 8
  equiv := ⟨BitVec.toFin ∘ Int8.toBitVec, Int8.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FinEnum Int16 where
  card := 2 ^ 16
  equiv := ⟨BitVec.toFin ∘ Int16.toBitVec, Int16.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FinEnum Int32 where
  card := 2 ^ 32
  equiv := ⟨BitVec.toFin ∘ Int32.toBitVec, Int32.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FinEnum Int64 where
  card := 2 ^ 64
  equiv := ⟨BitVec.toFin ∘ Int64.toBitVec, Int64.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩
/-
**FinEnum.** 是 Mathlib 中的一个实例，位于命名空间 `FinEnum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : FinEnum (BitVec n) where
  card := 2 ^ n
  equiv := ⟨BitVec.toFin, BitVec.ofFin, by intro x; simp, by intro x; simp⟩
/-
**FinEnum.card_UInt8** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：FinEnum.card UInt8 = 2 ^ 8
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma card_UInt8 : card UInt8 = 2 ^ 8 := rfl
/-
**FinEnum.card_UInt16** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：FinEnum.card UInt16 = 2 ^ 16
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma card_UInt16 : card UInt16 = 2 ^ 16 := rfl
/-
**FinEnum.card_UInt32** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：FinEnum.card UInt32 = 2 ^ 32
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma card_UInt32 : card UInt32 = 2 ^ 32 := rfl
/-
**FinEnum.card_UInt64** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：FinEnum.card UInt64 = 2 ^ 64
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma card_UInt64 : card UInt64 = 2 ^ 64 := rfl
/-
**FinEnum.card_Int8** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：FinEnum.card Int8 = 2 ^ 8
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma card_Int8 : card Int8 = 2 ^ 8 := rfl
/-
**FinEnum.card_Int16** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：FinEnum.card Int16 = 2 ^ 16
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma card_Int16 : card Int16 = 2 ^ 16 := rfl
/-
**FinEnum.card_Int32** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：FinEnum.card Int32 = 2 ^ 32
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma card_Int32 : card Int32 = 2 ^ 32 := rfl
/-
**FinEnum.card_Int64** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：FinEnum.card Int64 = 2 ^ 64
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma card_Int64 : card Int64 = 2 ^ 64 := rfl
/-
**FinEnum.card_bitVec** 是 Mathlib 中的一个定理，位于命名空间 `FinEnum`。
形式化陈述：∀ (n : ℕ), FinEnum.card (BitVec n) = 2 ^ n
参数：n : ℕ；BitVec n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma card_bitVec (n : ℕ) : card (BitVec n) = 2 ^ n := rfl

end FinEnum

namespace List
variable {α : Type*} [FinEnum α] {β : α → Type*} [∀ a, FinEnum (β a)]
open FinEnum

/-
**List.mem_pi_toList** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_pi_toList (xs : List α) (f : forall a, a in xs -> β a) : f in pi xs fu
n x => toList (β x)
参数：xs : List α；f : forall a, a in xs -> β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `List.mem_pi`：mem_pi {l : List ι} (fs : forall i, List (α i)) (f : forall
 i in l, α i) : (f in pi l fs) ↔ (forall i (hi : i in l), f i hi in fs i)
· 使用定理 `FinEnum.mem_toList`：mem_toList [FinEnum α] (x : α) : x in toList α
-/
theorem mem_pi_toList (xs : List α)
    (f : ∀ a, a ∈ xs → β a) : f ∈ pi xs fun x => toList (β x) :=
  (mem_pi _ _).mpr fun _ _ ↦ mem_toList _

/-- enumerate all functions whose domain and range are finitely enumerable -/
/-
**List.Pi.enum** 是 Mathlib 中的一个定义，位于命名空间 `List.Pi`。
形式化陈述：{α : Type u_1} → [FinEnum α] → (β : α → Type u_3) → [(a : α) → FinEnum (β 
a)] → List ((a : α) → β a)
参数：β : α → Type u_3；a : α；β a；(a : α) → β a。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FinEnum.mem_toList`：mem_toList [FinEnum α] (x : α) : x in toList α

--- 原说明 ---
enumerate all functions whose domain and range are finitely enumerable
-/
def Pi.enum (β : α → Type*) [∀ a, FinEnum (β a)] : List (∀ a, β a) :=
  (pi (toList α) fun x => toList (β x)).map (fun f x => f x (mem_toList _))
/-
**List.Pi.mem_enum** 是 Mathlib 中的一个定理，位于命名空间 `List.Pi`。
形式化陈述：∀ {α : Type u_1} [inst : FinEnum α] {β : α → Type u_2} [inst_1 : (a : α) →
 FinEnum (β a)] (f : (a : α) → β a),   f ∈ List.Pi.enum β
参数：a : α；β a；f : (a : α) → β a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FinEnum.mem_toList`：mem_toList [FinEnum α] (x : α) : x in toList α
· 使用定理 `List.mem_pi_toList`：mem_pi_toList (xs : List α) (f : forall a, a in xs -
> β a) : f in pi xs fun x => toList (β x)
-/
theorem Pi.mem_enum (f : ∀ a, β a) :
    f ∈ Pi.enum β := by simpa [Pi.enum] using ⟨fun a _ => f a, mem_pi_toList _ _, rfl⟩
/-
**List.Pi.finEnum** 是 Mathlib 中的一个定义，位于命名空间 `List.Pi`。
形式化陈述：{α : Type u_1} → [FinEnum α] → {β : α → Type u_2} → [(a : α) → FinEnum (β 
a)] → FinEnum ((a : α) → β a)
参数：a : α；β a；(a : α) → β a。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pi.mem_enum`：∀ {α : Type u_1} [inst : FinEnum α] {β : α → Type u_2}
 [inst_1 : (a : α) → FinEnum (β a)] (f : (a : α) → β a),   f ∈ List.Pi.enum β
-/
instance Pi.finEnum : FinEnum (∀ a, β a) :=
  ofList (Pi.enum _) fun _ => Pi.mem_enum _
/-
**List.pfunFinEnum** 是 Mathlib 中的一个实例，位于命名空间 `List`。
形式化陈述：pfunFinEnum (p : Prop) [Decidable p] (α : p -> Type) [forall hp, FinEnum (
α hp)] : FinEnum (forall hp : p, α hp)
参数：p : Prop；α : p -> Type；α hp。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pfunFinEnum (p : Prop) [Decidable p] (α : p → Type) [∀ hp, FinEnum (α hp)] :
    FinEnum (∀ hp : p, α hp) :=
  if hp : p then
    ofList ((toList (α hp)).map fun x _ => x) (by intro x; simpa using ⟨x hp, rfl⟩)
  else ofList [fun hp' => (hp hp').elim] (by simp [funext_iff, hp])

end List

