/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Set.Prod

/-!
# Finite products of types

This file defines the product of types over a list. For `l : List ι` and `α : ι → Type v` we define
`List.TProd α l = l.foldr (fun i β ↦ α i × β) PUnit`.
This type should not be used if `∀ i, α i` or `∀ i ∈ l, α i` can be used instead
(in the last expression, we could also replace the list `l` by a set or a finset).
This type is used as an intermediary between binary products and finitary products.
The application of this type is finitary product measures, but it could be used in any
construction/theorem that is easier to define/prove on binary products than on finitary products.

* Once we have the construction on binary products (like binary product measures in
  `MeasureTheory.prod`), we can easily define a finitary version on the type `TProd l α`
  by iterating. Properties can also be easily extended from the binary case to the finitary case
  by iterating.
* Then we can use the equivalence `List.TProd.piEquivTProd` below (or enhanced versions of it,
  like a `MeasurableEquiv` for product measures) to get the construction on `∀ i : ι, α i`, at
  least when assuming `[Fintype ι] [Encodable ι]` (using `Encodable.sortedUniv`).
  Using `attribute [local instance] Fintype.toEncodable` we can get rid of the argument
  `[Encodable ι]`.

## Main definitions

* We have the equivalence `TProd.piEquivTProd : (∀ i, α i) ≃ TProd α l`
  if `l` contains every element of `ι` exactly once.
* The product of sets is `Set.tprod : (∀ i, Set (α i)) → Set (TProd α l)`.
-/

@[expose] public section


open List Function
universe u v
variable {ι : Type u} {α : ι → Type v} {i j : ι} {l : List ι}

namespace List

variable (α) in
/-- The product of a family of types over a list. -/
/-
**List.TProd** 是 Mathlib 中的一个缩写定义，位于命名空间 `List`。
形式化陈述：TProd (l : List ι) : Type v
参数：l : List ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a family of types over a list.
-/
abbrev TProd (l : List ι) : Type v :=
  l.foldr (fun i β => α i × β) PUnit

namespace TProd

/-- Turning a function `f : ∀ i, α i` into an element of the iterated product `TProd α l`. -/
/-
**List.TProd.mk** 是 Mathlib 中的一个定义，位于命名空间 `List.TProd`。
形式化陈述：{ι : Type u} → {α : ι → Type v} → (l : List ι) → ((i : ι) → α i) → List.TP
rod α l
参数：l : List ι；(i : ι) → α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turning a function `f : ∀ i, α i` into an element of the iterated product `TProd
 α l`.
-/
protected def mk : ∀ (l : List ι) (_f : ∀ i, α i), TProd α l
  | [] => fun _ => PUnit.unit
  | i :: is => fun f => (f i, TProd.mk is f)
/-
**List.TProd.** 是 Mathlib 中的一个实例，位于命名空间 `List.TProd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Inhabited (α i)] : Inhabited (TProd α l) :=
  ⟨TProd.mk l default⟩

@[simp]
/-
**List.TProd.fst_mk** 是 Mathlib 中的一个定理，位于命名空间 `List.TProd`。
形式化陈述：fst_mk (i : ι) (l : List ι) (f : forall i, α i) : (TProd.mk (i :: l) f).1 
= f i
参数：i : ι；l : List ι；f : forall i, α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_mk (i : ι) (l : List ι) (f : ∀ i, α i) : (TProd.mk (i :: l) f).1 = f i :=
  rfl

@[simp]
/-
**List.TProd.snd_mk** 是 Mathlib 中的一个定理，位于命名空间 `List.TProd`。
形式化陈述：snd_mk (i : ι) (l : List ι) (f : forall i, α i) : (TProd.mk.{u, v} (i :: l
) f).2 = TProd.mk.{u, v} l f
参数：i : ι；l : List ι；f : forall i, α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_mk (i : ι) (l : List ι) (f : ∀ i, α i) :
    (TProd.mk.{u, v} (i :: l) f).2 = TProd.mk.{u, v} l f :=
  rfl

variable [DecidableEq ι]

/-- Given an element of the iterated product `l.Prod α`, take a projection into direction `i`.
  If `i` appears multiple times in `l`, this chooses the first component in direction `i`. -/
/-
**List.TProd.elim** 是 Mathlib 中的一个定义，位于命名空间 `List.TProd`。
形式化陈述：{ι : Type u} → {α : ι → Type v} → [DecidableEq ι] → {l : List ι} → List.TP
rod α l → {i : ι} → i ∈ l → α i
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an element of the iterated product `l.Prod α`, take a projection into dire
ction `i`.
  If `i` appears multiple times in `l`, this chooses the first component in dire
ction `i`.
-/
protected def elim : ∀ {l : List ι} (_ : TProd α l) {i : ι} (_ : i ∈ l), α i
  | i :: is, v, j, hj =>
    if hji : j = i then by
      subst hji
      exact v.1
    else TProd.elim v.2 ((List.mem_cons.mp hj).resolve_left hji)

@[simp]
/-
**List.TProd.elim_self** 是 Mathlib 中的一个定理，位于命名空间 `List.TProd`。
形式化陈述：elim_self (v : TProd α (i :: l)) : v.elim mem_cons_self = v.1
参数：v : TProd α (i :: l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem elim_self (v : TProd α (i :: l)) : v.elim mem_cons_self = v.1 := by simp [TProd.elim]

@[simp]
/-
**List.TProd.elim_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `List.TProd`。
形式化陈述：elim_of_ne (hj : j in i :: l) (hji : j != i) (v : TProd α (i :: l)) : v.el
im hj = TProd.elim v.2 ((List.mem_cons.mp hj).resolve_left hji)
参数：hj : j in i :: l；hji : j != i；v : TProd α (i :: l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem elim_of_ne (hj : j ∈ i :: l) (hji : j ≠ i) (v : TProd α (i :: l)) :
    v.elim hj = TProd.elim v.2 ((List.mem_cons.mp hj).resolve_left hji) := by simp [TProd.elim, hji]

@[simp]
/-
**List.TProd.elim_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List.TProd`。
形式化陈述：elim_of_mem (hl : (i :: l).Nodup) (hj : j in l) (v : TProd α (i :: l)) : v
.elim (mem_cons_of_mem _ hj) = TProd.elim v.2 hj
参数：hl : (i :: l).Nodup；hj : j in l；v : TProd α (i :: l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TProd.elim_of_ne`：elim_of_ne (hj : j in i :: l) (hji : j != i) (v :
 TProd α (i :: l)) : v.elim hj = TProd.elim v.2 ((List.mem_cons.mp hj).resolve_l
eft hji)
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `List.Nodup.notMem`：∀ {α : Type u} {l : List α} {a : α}, (a :: l).Nodup →
 a ∉ l
-/
theorem elim_of_mem (hl : (i :: l).Nodup) (hj : j ∈ l) (v : TProd α (i :: l)) :
    v.elim (mem_cons_of_mem _ hj) = TProd.elim v.2 hj := by
  apply elim_of_ne
  rintro rfl
  exact hl.notMem hj
/-
**List.TProd.elim_mk** 是 Mathlib 中的一个定理，位于命名空间 `List.TProd`。
形式化陈述：∀ {ι : Type u} {α : ι → Type v} [inst : DecidableEq ι] (l : List ι) (f : (
i : ι) → α i) {i : ι} (hi : i ∈ l),   (List.TProd.mk l f).elim hi = f i
参数：l : List ι；f : (i : ι) → α i；hi : i ∈ l；List.TProd.mk l f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem elim_mk : ∀ (l : List ι) (f : ∀ i, α i) {i : ι} (hi : i ∈ l), (TProd.mk l f).elim hi = f i
  | i :: is, f, j, hj => by
    by_cases hji : j = i
    · subst hji
      simp
    · rw [TProd.elim_of_ne _ hji, snd_mk, elim_mk is]

@[ext]
/-
**List.TProd.ext** 是 Mathlib 中的一个定理，位于命名空间 `List.TProd`。
形式化陈述：∀ {ι : Type u} {α : ι → Type v} [inst : DecidableEq ι] {l : List ι},   l.N
odup → ∀ {v w : List.TProd α l}, (∀ (i : ι) (hi : i ∈ l), v.elim hi = w.elim hi)
 → v = w
参数：∀ (i : ι) (hi : i ∈ l), v.elim hi = w.elim hi。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ext :
    ∀ {l : List ι} (_ : l.Nodup) {v w : TProd α l}
      (_ : ∀ (i) (hi : i ∈ l), v.elim hi = w.elim hi), v = w
  | [], _, v, w, _ => PUnit.ext v w
  | i :: is, hl, v, w, hvw => by
    apply Prod.ext
    · rw [← elim_self v, hvw, elim_self]
    refine ext (nodup_cons.mp hl).2 fun j hj => ?_
    rw [← elim_of_mem hl, hvw, elim_of_mem hl]

/-- A version of `TProd.elim` when `l` contains all elements. In this case we get a function into
  `Π i, α i`. -/
@[simp]
/-
**List.TProd.elim'** 是 Mathlib 中的一个定义，位于命名空间 `List.TProd`。
形式化陈述：{ι : Type u} → {α : ι → Type v} → {l : List ι} → [DecidableEq ι] → (∀ (i :
 ι), i ∈ l) → List.TProd α l → (i : ι) → α i
参数：∀ (i : ι), i ∈ l；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `TProd.elim` when `l` contains all elements. In this case we get a 
function into
  `Π i, α i`.
-/
protected def elim' (h : ∀ i, i ∈ l) (v : TProd α l) (i : ι) : α i :=
  v.elim (h i)
/-
**List.TProd.mk_elim** 是 Mathlib 中的一个定理，位于命名空间 `List.TProd`。
形式化陈述：mk_elim (hnd : l.Nodup) (h : forall i, i in l) (v : TProd α l) : TProd.mk 
l (v.elim' h) = v
参数：hnd : l.Nodup；h : forall i, i in l；v : TProd α l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TProd.ext`：∀ {ι : Type u} {α : ι → Type v} [inst : DecidableEq ι] {
l : List ι},   l.Nodup → ∀ {v w : List.TProd α l}, (∀ (i : ι) (hi : i ∈ l), v.el
im h…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.TProd.elim_mk`：∀ {ι : Type u} {α : ι → Type v} [inst : DecidableEq 
ι] (l : List ι) (f : (i : ι) → α i) {i : ι} (hi : i ∈ l),   (List.TProd.mk l f).
elim hi …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_elim (hnd : l.Nodup) (h : ∀ i, i ∈ l) (v : TProd α l) : TProd.mk l (v.elim' h) = v :=
  TProd.ext hnd fun i hi => by simp [elim_mk]

/-- Pi-types are equivalent to iterated products. -/
/-
**List.TProd.piEquivTProd** 是 Mathlib 中的一个定义，位于命名空间 `List.TProd`。
形式化陈述：piEquivTProd (hnd : l.Nodup) (h : forall i, i in l) : (forall i, α i) ≃ TP
rod α l
参数：hnd : l.Nodup；h : forall i, i in l。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.TProd.mk_elim`：mk_elim (hnd : l.Nodup) (h : forall i, i in l) (v : 
TProd α l) : TProd.mk l (v.elim' h) = v

--- 原说明 ---
Pi-types are equivalent to iterated products.
-/
def piEquivTProd (hnd : l.Nodup) (h : ∀ i, i ∈ l) : (∀ i, α i) ≃ TProd α l :=
  ⟨TProd.mk l, TProd.elim' h, fun f => funext fun i => elim_mk l f (h i), mk_elim hnd h⟩

end TProd

end List

namespace Set

/-- A product of sets in `TProd α l`. -/
@[simp]
/-
**Set.tprod** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{ι : Type u} → {α : ι → Type v} → (l : List ι) → ((i : ι) → Set (α i)) → S
et (List.TProd α l)
参数：l : List ι；(i : ι) → Set (α i)；List.TProd α l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product of sets in `TProd α l`.
-/
protected def tprod : ∀ (l : List ι) (_t : ∀ i, Set (α i)), Set (TProd α l)
  | [], _ => univ
  | i :: is, t => t i ×ˢ Set.tprod is t

set_option backward.isDefEq.respectTransparency false in
/-
**Set.mk_preimage_tprod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_tprod : forall (l : List ι) (t : forall i, Set (α i)), TProd.m
k l ⁻¹' Set.tprod l t = { i | i in l }.pi t | [], t => by simp [Set.tprod] | i :
: l, t => by ext f have h : TProd.mk l f in Set.tprod l t ↔ forall i : ι, i in l
 -> f i in t i
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_tprod :
    ∀ (l : List ι) (t : ∀ i, Set (α i)), TProd.mk l ⁻¹' Set.tprod l t = { i | i ∈ l }.pi t
  | [], t => by simp [Set.tprod]
  | i :: l, t => by
    ext f
    have h : TProd.mk l f ∈ Set.tprod l t ↔ ∀ i : ι, i ∈ l → f i ∈ t i := by
      change f ∈ TProd.mk l ⁻¹' Set.tprod l t ↔ f ∈ { x | x ∈ l }.pi t
      rw [mk_preimage_tprod l t]
    -- `simp [Set.TProd, TProd.mk, this]` can close this goal but is slow.
    rw [Set.tprod, TProd.mk, mem_preimage, mem_pi, prodMk_mem_set_prod_eq]
    simp_rw [mem_ofPred_eq, mem_cons]
    rw [forall_eq_or_imp, and_congr_right_iff]
    exact fun _ => h
/-
**Set.elim_preimage_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：elim_preimage_pi [DecidableEq ι] {l : List ι} (hnd : l.Nodup) (h : forall 
i, i in l) (t : forall i, Set (α i)) : TProd.elim' h ⁻¹' pi univ t = Set.tprod l
 t
参数：hnd : l.Nodup；h : forall i, i in l；t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mk_preimage_tprod`：mk_preimage_tprod : forall (l : List ι) (t : fora
ll i, Set (α i)), TProd.mk l ⁻¹' Set.tprod l t = { i | i in l }.pi t | [], t => 
by simp [Se…
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `List.TProd.mk_elim`：mk_elim (hnd : l.Nodup) (h : forall i, i in l) (v : 
TProd α l) : TProd.mk l (v.elim' h) = v
-/
theorem elim_preimage_pi [DecidableEq ι] {l : List ι} (hnd : l.Nodup) (h : ∀ i, i ∈ l)
    (t : ∀ i, Set (α i)) : TProd.elim' h ⁻¹' pi univ t = Set.tprod l t := by
  have h2 : { i | i ∈ l } = univ := by
    ext i
    simp [h]
  rw [← h2, ← mk_preimage_tprod, preimage_preimage]
  simp only [TProd.mk_elim hnd h]
  dsimp

end Set

