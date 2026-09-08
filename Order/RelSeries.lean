/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/
module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Rel
public import Mathlib.Order.OrderIsoNat

/-!
# Series of a relation

If `r` is a relation on `α` then a relation series of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`

-/

@[expose] public section

open scoped SetRel

variable {α : Type*} (r : SetRel α α)
variable {β : Type*} (s : SetRel β β)

/--
Let `r` be a relation on `α`, a relation series of `r` of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`
-/
/-
**RelSeries** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → SetRel α α → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `r` be a relation on `α`, a relation series of `r` of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`
-/
structure RelSeries where
  /-- The number of inequalities in the series -/
  length : ℕ
  /-- The underlying function of a relation series -/
  toFun : Fin (length + 1) → α
  /-- Adjacent elements are related -/
  step : ∀ (i : Fin length), toFun (Fin.castSucc i) ~[r] toFun i.succ

namespace RelSeries

/-
**RelSeries.** 是 Mathlib 中的一个实例，位于命名空间 `RelSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (RelSeries r) (fun x ↦ Fin (x.length + 1) → α) :=
{ coe := RelSeries.toFun }

/--
For any type `α`, each term of `α` gives a relation series with the right most index to be 0.
-/
/-
**RelSeries.singleton** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：{α : Type u_1} → (r : SetRel α α) → α → RelSeries r
参数：r : SetRel α α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any type `α`, each term of `α` gives a relation series with the right most i
ndex to be 0.
-/
@[simps!] def singleton (a : α) : RelSeries r where
  length := 0
  toFun _ := a
  step := Fin.elim0
/-
**RelSeries.** 是 Mathlib 中的一个实例，位于命名空间 `RelSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : IsEmpty (RelSeries r) where
  false x := IsEmpty.false (x 0)
/-
**RelSeries.** 是 Mathlib 中的一个实例，位于命名空间 `RelSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (RelSeries r) where
  default := singleton r default
/-
**RelSeries.** 是 Mathlib 中的一个实例，位于命名空间 `RelSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nonempty (RelSeries r) :=
  Nonempty.map (singleton r) inferInstance

variable {r}

@[ext (iff := false)]
/-
**RelSeries.ext** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：ext {x y : RelSeries r} (length_eq : x.length = y.length) (toFun_eq : x.to
Fun = y.toFun ∘ Fin.cast (by rw [length_eq])) : x = y
参数：length_eq : x.length = y.length；toFun_eq : x.toFun = y.toFun ∘ Fin.cast (by r
w [length_eq])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cast_refl`：∀ (n : ℕ) (h : n = n), Fin.cast h = id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RelSeries.mk.congr_simp`：∀ {α : Type u_1} {r : SetRel α α} (length : ℕ) 
(toFun toFun_1 : Fin (length + 1) → α) (e_toFun : toFun = toFun_1)   (step : ∀ (
i : Fin lengt…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ext {x y : RelSeries r} (length_eq : x.length = y.length)
    (toFun_eq : x.toFun = y.toFun ∘ Fin.cast (by rw [length_eq])) : x = y := by
  rcases x with ⟨nx, fx⟩
  dsimp only at length_eq
  subst length_eq
  simp_all
/-
**RelSeries.rel_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：rel_of_lt [r.IsTrans] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i 
< j) : x i ~[r] x j
参数：x : RelSeries r；x.length + 1；h : i < j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.liftFun_iff_succ`：liftFun_iff_succ {α : Type*} (r : α -> α -> Prop) 
[IsTrans α r] {f : Fin (n + 1) -> α} : ((· < ·) ⇒ r) f f ↔ forall i : Fin n, r (
f (castSuc…
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
-/
lemma rel_of_lt [r.IsTrans] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i < j) :
    x i ~[r] x j :=
  (Fin.liftFun_iff_succ (· ~[r] ·)).mpr x.step h
/-
**RelSeries.rel_or_eq_of_le** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：rel_or_eq_of_le [r.IsTrans] (x : RelSeries r) {i j : Fin (x.length + 1)} (
h : i <= j) : x i ~[r] x j ∨ x i = x j
参数：x : RelSeries r；x.length + 1；h : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用引理 `RelSeries.rel_of_lt`：rel_of_lt [r.IsTrans] (x : RelSeries r) {i j : Fin 
(x.length + 1)} (h : i < j) : x i ~[r] x j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.lt_or_eq_of_le`：∀ {n : ℕ} {a b : Fin n}, a ≤ b → a < b ∨ a = b
-/
lemma rel_or_eq_of_le [r.IsTrans] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i ≤ j) :
    x i ~[r] x j ∨ x i = x j :=
  (Fin.lt_or_eq_of_le h).imp (x.rel_of_lt ·) (by rw [·])

/--
Given two relations `r, s` on `α` such that `r ≤ s`, any relation series of `r` induces a relation
series of `s`
-/
@[simps!]
/-
**RelSeries.ofLE** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：ofLE (x : RelSeries r) {s : SetRel α α} (h : r <= s) : RelSeries s where l
ength
参数：x : RelSeries r；h : r <= s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two relations `r, s` on `α` such that `r ≤ s`, any relation series of `r` 
induces a relation
series of `s`
-/
def ofLE (x : RelSeries r) {s : SetRel α α} (h : r ≤ s) : RelSeries s where
  length := x.length
  toFun := x
  step _ := h <| x.step _
/-
**RelSeries.coe_ofLE** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：coe_ofLE (x : RelSeries r) {s : SetRel α α} (h : r <= s) : (x.ofLE h : _ -
> _) = x
参数：x : RelSeries r；h : r <= s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_ofLE (x : RelSeries r) {s : SetRel α α} (h : r ≤ s) :
    (x.ofLE h : _ → _) = x := rfl

/-- Every relation series gives a list -/
/-
**RelSeries.toList** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：toList (x : RelSeries r) : List α
参数：x : RelSeries r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every relation series gives a list
-/
def toList (x : RelSeries r) : List α := List.ofFn x

@[simp]
/-
**RelSeries.length_toList** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：length_toList (x : RelSeries r) : x.toList.length = x.length + 1
参数：x : RelSeries r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
-/
lemma length_toList (x : RelSeries r) : x.toList.length = x.length + 1 :=
  List.length_ofFn

@[simp]
/-
**RelSeries.toList_singleton** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：toList_singleton (x : α) : (singleton r x).toList = [x]
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_succ`：∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofF
n f = f 0 :: List.ofFn fun i => f i.succ
· 使用定理 `List.ofFn_zero`：∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toList_singleton (x : α) : (singleton r x).toList = [x] := by simp [toList, singleton]
/-
**RelSeries.isChain_toList** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：isChain_toList (x : RelSeries r) : x.toList.IsChain (· ~[r] ·)
参数：x : RelSeries r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RelSeries.length_toList`：length_toList (x : RelSeries r) : x.toList.leng
th = x.length + 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.get_ofFn`：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i = f (F
in.cast (by simp) i)
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
-/
lemma isChain_toList (x : RelSeries r) : x.toList.IsChain (· ~[r] ·) := by
  simp_rw [List.isChain_iff_getElem, length_toList, add_lt_add_iff_right]
  intro i h
  convert! x.step ⟨i, by simpa [toList] using h⟩ <;> apply List.get_ofFn
/-
**RelSeries.toList_ne_nil** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：toList_ne_nil (x : RelSeries r) : x.toList != []
参数：x : RelSeries r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.eq_nil_iff_forall_not_mem`：∀ {α : Type u_1} {l : List α}, l = [] ↔ 
∀ (a : α), a ∉ l
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_ofFn`：∀ {α : Type u_1} {n : ℕ} {f : Fin n → α} {a : α}, a ∈ Lis
t.ofFn f ↔ ∃ i, f i = a
-/
lemma toList_ne_nil (x : RelSeries r) : x.toList ≠ [] := fun m =>
  List.eq_nil_iff_forall_not_mem.mp m (x 0) <| List.mem_ofFn.mpr ⟨_, rfl⟩

/-- Every nonempty list satisfying the chain condition gives a relation series -/
@[simps]
/-
**RelSeries.fromListIsChain** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：fromListIsChain (x : List α) (x_ne_nil : x != []) (hx : x.IsChain (· ~[r] 
·)) : RelSeries r where length
参数：x : List α；x_ne_nil : x != []；hx : x.IsChain (· ~[r] ·)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every nonempty list satisfying the chain condition gives a relation series
-/
def fromListIsChain (x : List α) (x_ne_nil : x ≠ []) (hx : x.IsChain (· ~[r] ·)) : RelSeries r where
  length := x.length - 1
  toFun i := x[Fin.cast (Nat.succ_pred_eq_of_pos <| List.length_pos_iff.mpr x_ne_nil) i]
  step i := List.isChain_iff_getElem.mp hx i _

set_option backward.isDefEq.respectTransparency false in
/-- Relation series of `r` and nonempty list of `α` satisfying `r`-chain condition bijectively
corresponds to each other. -/
/-
**RelSeries.Equiv** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：{α : Type u_1} → {r : SetRel α α} → RelSeries r ≃ ↑{x | x ≠ [] ∧ List.IsCh
ain (fun x1 x2 => (x1, x2) ∈ r) x}
参数：fun x1 x2 => (x1, x2) ∈ r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relation series of `r` and nonempty list of `α` satisfying `r`-chain condition b
ijectively
corresponds to each other.
-/
protected def Equiv : RelSeries r ≃ {x : List α | x ≠ [] ∧ x.IsChain (· ~[r] ·)} where
  toFun x := ⟨_, x.toList_ne_nil, x.isChain_toList⟩
  invFun x := fromListIsChain _ x.2.1 x.2.2
  left_inv x := ext (by simp [toList]) <| by ext; dsimp; apply List.get_ofFn
  right_inv x := by
    refine Subtype.ext (List.ext_get ?_ fun n hn1 _ => by dsimp; apply List.get_ofFn)
    have := Nat.succ_pred_eq_of_pos <| List.length_pos_iff.mpr x.2.1
    simp_all [toList]
/-
**RelSeries.toList_injective** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：toList_injective : Function.Injective (RelSeries.toList (r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma toList_injective : Function.Injective (RelSeries.toList (r := r)) :=
  fun _ _ h ↦ (RelSeries.Equiv).injective <| Subtype.ext h

-- TODO : build a similar bijection between `RelSeries α` and `Quiver.Path`

end RelSeries

namespace SetRel

/-- A relation `r` is said to be finite dimensional iff there is a relation series of `r` with the
  maximum length. -/
@[mk_iff]
/-
**SetRel.FiniteDimensional** 是 Mathlib 中的一个归纳类型，位于命名空间 `SetRel`。
形式化陈述：{α : Type u_1} → SetRel α α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation `r` is said to be finite dimensional iff there is a relation series o
f `r` with the
  maximum length.
-/
class FiniteDimensional : Prop where
  /-- A relation `r` is said to be finite dimensional iff there is a relation series of `r` with the
  maximum length. -/
  exists_longest_relSeries : ∃ x : RelSeries r, ∀ y : RelSeries r, y.length ≤ x.length

/-- A relation `r` is said to be infinite dimensional iff there exists relation series of arbitrary
  length. -/
@[mk_iff]
/-
**SetRel.InfiniteDimensional** 是 Mathlib 中的一个归纳类型，位于命名空间 `SetRel`。
形式化陈述：{α : Type u_1} → SetRel α α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation `r` is said to be infinite dimensional iff there exists relation seri
es of arbitrary
  length.
-/
class InfiniteDimensional : Prop where
  /-- A relation `r` is said to be infinite dimensional iff there exists relation series of
  arbitrary length. -/
  exists_relSeries_with_length : ∀ n : ℕ, ∃ x : RelSeries r, x.length = n

end SetRel

namespace RelSeries

/-- The longest relational series when a relation is finite dimensional -/
/-
**RelSeries.longestOf** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：{α : Type u_1} → (r : SetRel α α) → [r.FiniteDimensional] → RelSeries r
参数：r : SetRel α α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.FiniteDimensional.exists_longest_relSeries`：∀ {α : Type u_1} {r :
 SetRel α α} [self : r.FiniteDimensional], ∃ x, ∀ (y : RelSeries r), y.length ≤ 
x.length

--- 原说明 ---
The longest relational series when a relation is finite dimensional
-/
protected noncomputable def longestOf [r.FiniteDimensional] : RelSeries r :=
  SetRel.FiniteDimensional.exists_longest_relSeries.choose
/-
**RelSeries.length_le_length_longestOf** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：length_le_length_longestOf [r.FiniteDimensional] (x : RelSeries r) : x.len
gth <= (RelSeries.longestOf r).length
参数：x : RelSeries r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `SetRel.FiniteDimensional.exists_longest_relSeries`：∀ {α : Type u_1} {r :
 SetRel α α} [self : r.FiniteDimensional], ∃ x, ∀ (y : RelSeries r), y.length ≤ 
x.length
-/
lemma length_le_length_longestOf [r.FiniteDimensional] (x : RelSeries r) :
    x.length ≤ (RelSeries.longestOf r).length :=
  SetRel.FiniteDimensional.exists_longest_relSeries.choose_spec _

/-- A relation series with length `n` if the relation is infinite dimensional -/
/-
**RelSeries.withLength** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：{α : Type u_1} → (r : SetRel α α) → [r.InfiniteDimensional] → ℕ → RelSerie
s r
参数：r : SetRel α α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.InfiniteDimensional.exists_relSeries_with_length`：∀ {α : Type u_1
} {r : SetRel α α} [self : r.InfiniteDimensional] (n : ℕ), ∃ x, x.length = n

--- 原说明 ---
A relation series with length `n` if the relation is infinite dimensional
-/
protected noncomputable def withLength [r.InfiniteDimensional] (n : ℕ) : RelSeries r :=
  (SetRel.InfiniteDimensional.exists_relSeries_with_length n).choose
/-
**RelSeries.length_withLength** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} (r : SetRel α α) [inst : r.InfiniteDimensional] (n : ℕ), 
(RelSeries.withLength r n).length = n
参数：r : SetRel α α；n : ℕ；RelSeries.withLength r n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `SetRel.InfiniteDimensional.exists_relSeries_with_length`：∀ {α : Type u_1
} {r : SetRel α α} [self : r.InfiniteDimensional] (n : ℕ), ∃ x, x.length = n
-/
@[simp] lemma length_withLength [r.InfiniteDimensional] (n : ℕ) :
    (RelSeries.withLength r n).length = n :=
  (SetRel.InfiniteDimensional.exists_relSeries_with_length n).choose_spec

section
variable {r} {s : RelSeries r} {x : α}

/-- If a relation on `α` is infinite dimensional, then `α` is nonempty. -/
/-
**RelSeries.nonempty_of_infiniteDimensional** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries
`。
形式化陈述：nonempty_of_infiniteDimensional [r.InfiniteDimensional] : Nonempty α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
If a relation on `α` is infinite dimensional, then `α` is nonempty.
-/
lemma nonempty_of_infiniteDimensional [r.InfiniteDimensional] : Nonempty α :=
  ⟨RelSeries.withLength r 0 0⟩
/-
**RelSeries.nonempty_of_finiteDimensional** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：nonempty_of_finiteDimensional [r.FiniteDimensional] : Nonempty α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetRel.finiteDimensional_iff`：∀ {α : Type u_1} (r : SetRel α α), r.Finit
eDimensional ↔ ∃ x, ∀ (y : RelSeries r), y.length ≤ x.length
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma nonempty_of_finiteDimensional [r.FiniteDimensional] : Nonempty α := by
  obtain ⟨p, _⟩ := (r.finiteDimensional_iff).mp ‹_›
  exact ⟨p 0⟩
/-
**RelSeries.membership** 是 Mathlib 中的一个实例，位于命名空间 `RelSeries`。
形式化陈述：membership : Membership α (RelSeries r)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance membership : Membership α (RelSeries r) :=
  ⟨Function.swap (· ∈ Set.range ·)⟩
/-
**RelSeries.mem_def** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：mem_def : x in s ↔ x in Set.range s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_def : x ∈ s ↔ x ∈ Set.range s := Iff.rfl
/-
**RelSeries.mem_toList** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} {s : RelSeries r} {x : α}, x ∈ s.toList 
↔ x ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.toList.eq_1`：∀ {α : Type u_1} {r : SetRel α α} (x : RelSeries 
r), x.toList = List.ofFn x.toFun
· 使用定理 `List.mem_ofFn'`：mem_ofFn' {n} (f : Fin n -> α) (a : α) : a in ofFn f ↔ a
 in Set.range f
· 使用定理 `RelSeries.mem_def`：mem_def : x in s ↔ x in Set.range s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_toList : x ∈ s.toList ↔ x ∈ s := by
  rw [RelSeries.toList, List.mem_ofFn', RelSeries.mem_def]
/-
**RelSeries.subsingleton_of_length_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`
。
形式化陈述：subsingleton_of_length_eq_zero (hs : s.length = 0) : {x | x in s}.Subsingl
eton
参数：hs : s.length = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
-/
theorem subsingleton_of_length_eq_zero (hs : s.length = 0) : {x | x ∈ s}.Subsingleton := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  congr!
  exact finCongr (by rw [hs, zero_add]) |>.injective <| Subsingleton.elim (α := Fin 1) _ _
/-
**RelSeries.length_ne_zero_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：length_ne_zero_of_nontrivial (h : {x | x in s}.Nontrivial) : s.length != 0
参数：h : {x | x in s}.Nontrivial。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nontrivial.not_subsingleton`：∀ {α : Type u} {s : Set α}, s.Nontrivia
l → ¬s.Subsingleton
· 使用定理 `RelSeries.subsingleton_of_length_eq_zero`：subsingleton_of_length_eq_zero
 (hs : s.length = 0) : {x | x in s}.Subsingleton
-/
theorem length_ne_zero_of_nontrivial (h : {x | x ∈ s}.Nontrivial) : s.length ≠ 0 :=
  fun hs ↦ h.not_subsingleton <| subsingleton_of_length_eq_zero hs
/-
**RelSeries.length_pos_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：length_pos_of_nontrivial (h : {x | x in s}.Nontrivial) : 0 < s.length
参数：h : {x | x in s}.Nontrivial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `RelSeries.length_ne_zero_of_nontrivial`：length_ne_zero_of_nontrivial (h 
: {x | x in s}.Nontrivial) : s.length != 0
-/
theorem length_pos_of_nontrivial (h : {x | x ∈ s}.Nontrivial) : 0 < s.length :=
  Nat.pos_iff_ne_zero.mpr <| length_ne_zero_of_nontrivial h
/-
**RelSeries.length_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：length_ne_zero [r.IsIrrefl] : s.length != 0 ↔ {x | x in s}.Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SetRel.irrefl`：∀ {α : Type u_1} (R : SetRel α α) (a : α) [R.IsIrrefl], (
a, a) ∉ R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
· 使用定理 `RelSeries.length_ne_zero_of_nontrivial`：length_ne_zero_of_nontrivial (h 
: {x | x in s}.Nontrivial) : s.length != 0
-/
theorem length_ne_zero [r.IsIrrefl] : s.length ≠ 0 ↔ {x | x ∈ s}.Nontrivial := by
  refine ⟨fun h ↦ ⟨s 0, by simp [mem_def], s 1, by simp [mem_def],
    fun rid ↦ r.irrefl (s 0) ?_⟩, length_ne_zero_of_nontrivial⟩
  nth_rw 2 [rid]
  convert! s.step ⟨0, by lia⟩
  ext
  simpa [Nat.pos_iff_ne_zero]
/-
**RelSeries.length_pos** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：length_pos [r.IsIrrefl] : 0 < s.length ↔ {x | x in s}.Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `RelSeries.length_ne_zero`：length_ne_zero [r.IsIrrefl] : s.length != 0 ↔ 
{x | x in s}.Nontrivial
-/
theorem length_pos [r.IsIrrefl] : 0 < s.length ↔ {x | x ∈ s}.Nontrivial :=
  Nat.pos_iff_ne_zero.trans length_ne_zero
/-
**RelSeries.length_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：length_eq_zero [r.IsIrrefl] : s.length = 0 ↔ {x | x in s}.Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `RelSeries.length_ne_zero`：length_ne_zero [r.IsIrrefl] : s.length != 0 ↔ 
{x | x in s}.Nontrivial
· 使用定理 `Set.not_nontrivial_iff`：not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingle
ton
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma length_eq_zero [r.IsIrrefl] : s.length = 0 ↔ {x | x ∈ s}.Subsingleton := by
  rw [← not_ne_iff, length_ne_zero, Set.not_nontrivial_iff]

/-- Start of a series, i.e. for `a₀ -r→ a₁ -r→ ... -r→ aₙ`, its head is `a₀`.

Since a relation series is assumed to be non-empty, this is well defined. -/
/-
**RelSeries.head** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：head (x : RelSeries r) : α
参数：x : RelSeries r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Start of a series, i.e. for `a₀ -r→ a₁ -r→ ... -r→ aₙ`, its head is `a₀`.

Since a relation series is assumed to be non-empty, this is well defined.
-/
def head (x : RelSeries r) : α := x 0

/-- End of a series, i.e. for `a₀ -r→ a₁ -r→ ... -r→ aₙ`, its last element is `aₙ`.

Since a relation series is assumed to be non-empty, this is well defined. -/
/-
**RelSeries.last** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：last (x : RelSeries r) : α
参数：x : RelSeries r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
End of a series, i.e. for `a₀ -r→ a₁ -r→ ... -r→ aₙ`, its last element is `aₙ`.

Since a relation series is assumed to be non-empty, this is well defined.
-/
def last (x : RelSeries r) : α := x <| Fin.last _
/-
**RelSeries.apply_zero** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：apply_zero (p : RelSeries r) : p 0 = p.head
参数：p : RelSeries r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma apply_zero (p : RelSeries r) : p 0 = p.head := rfl
/-
**RelSeries.apply_last** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：apply_last (x : RelSeries r) : x (Fin.last <| x.length) = x.last
参数：x : RelSeries r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma apply_last (x : RelSeries r) : x (Fin.last <| x.length) = x.last := rfl
/-
**RelSeries.head_mem** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：head_mem (x : RelSeries r) : x.head in x
参数：x : RelSeries r。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma head_mem (x : RelSeries r) : x.head ∈ x := ⟨_, rfl⟩
/-
**RelSeries.last_mem** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：last_mem (x : RelSeries r) : x.last in x
参数：x : RelSeries r。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma last_mem (x : RelSeries r) : x.last ∈ x := ⟨_, rfl⟩

@[simp]
/-
**RelSeries.head_singleton** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：head_singleton {r : SetRel α α} (x : α) : (singleton r x).head = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma head_singleton {r : SetRel α α} (x : α) : (singleton r x).head = x := by
  simp [singleton, head]

@[simp]
/-
**RelSeries.last_singleton** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：last_singleton {r : SetRel α α} (x : α) : (singleton r x).last = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.last_zero`：Fin.last 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma last_singleton {r : SetRel α α} (x : α) : (singleton r x).last = x := by
  simp [singleton, last]

@[simp]
/-
**RelSeries.head_toList** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：head_toList (p : RelSeries r) : p.toList.head p.toList_ne_nil = p.head
参数：p : RelSeries r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用引理 `RelSeries.toList_ne_nil`：toList_ne_nil (x : RelSeries r) : x.toList != [
]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.head.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = as_
1) (a : as ≠ []), as.head a = as_1.head ⋯
· 使用定理 `List.ofFn_succ`：∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofF
n f = f 0 :: List.ofFn fun i => f i.succ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma head_toList (p : RelSeries r) : p.toList.head p.toList_ne_nil = p.head := by
  simp [toList, apply_zero]

@[simp]
/-
**RelSeries.toList_getElem** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：toList_getElem (p : RelSeries r) {i : Nat} (hi : i < p.toList.length) : p.
toList[(i : Nat)] = p ⟨i, by simpa using hi⟩
参数：p : RelSeries r；hi : i < p.toList.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toList_getElem (p : RelSeries r) {i : ℕ} (hi : i < p.toList.length) :
    p.toList[(i : ℕ)] = p ⟨i, by simpa using hi⟩ := by
  simp only [toList, List.getElem_ofFn]
/-
**RelSeries.toList_getElem_zero_eq_head** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：toList_getElem_zero_eq_head (p : RelSeries r) : p.toList[0] = p.head
参数：p : RelSeries r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.toList_getElem`：toList_getElem (p : RelSeries r) {i : Nat} (hi
 : i < p.toList.length) : p.toList[(i : Nat)] = p ⟨i, by simpa using hi⟩
-/
lemma toList_getElem_zero_eq_head (p : RelSeries r) : p.toList[0] = p.head :=
  p.toList_getElem _

@[simp]
/-
**RelSeries.toList_fromListIsChain** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：toList_fromListIsChain (l : List α) (l_ne_nil : l != []) (hl : l.IsChain (
· ~[r] ·)) : (fromListIsChain l l_ne_nil hl).toList = l
参数：l : List α；l_ne_nil : l != []；hl : l.IsChain (· ~[r] ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
lemma toList_fromListIsChain (l : List α) (l_ne_nil : l ≠ []) (hl : l.IsChain (· ~[r] ·)) :
    (fromListIsChain l l_ne_nil hl).toList = l :=
  Subtype.ext_iff.mp <| RelSeries.Equiv.right_inv ⟨l, ⟨l_ne_nil, hl⟩⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**RelSeries.head_fromListIsChain** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：head_fromListIsChain (l : List α) (l_ne_nil : l != []) (hl : l.IsChain (· 
~[r] ·)) : (fromListIsChain l l_ne_nil hl).head = l.head l_ne_nil
参数：l : List α；l_ne_nil : l != []；hl : l.IsChain (· ~[r] ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.fromListIsChain_toFun`：∀ {α : Type u_1} {r : SetRel α α} (x : 
List α) (x_ne_nil : x ≠ []) (hx : List.IsChain (fun x1 x2 => (x1, x2) ∈ r) x)   
(i : Fin (x.length - …
· 使用定理 `List.getElem_zero_eq_head`：∀ {α : Type u_1} {l : List α} (h : 0 < l.leng
th), l[0] = l.head ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma head_fromListIsChain (l : List α) (l_ne_nil : l ≠ []) (hl : l.IsChain (· ~[r] ·)) :
    (fromListIsChain l l_ne_nil hl).head = l.head l_ne_nil := by
  simp [← apply_zero, List.getElem_zero_eq_head]

@[simp]
/-
**RelSeries.getLast_toList** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：getLast_toList (p : RelSeries r) : p.toList.getLast (by simp [toList]) = p
.last
参数：p : RelSeries r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma getLast_toList (p : RelSeries r) : p.toList.getLast (by simp [toList]) = p.last := by
  grind [length_toList, last, Fin.last, toList_getElem]

end

variable {r s}

/--
If `a₀ -r→ a₁ -r→ ... -r→ aₙ` and `b₀ -r→ b₁ -r→ ... -r→ bₘ` are two strict series
such that `r aₙ b₀`, then there is a chain of length `n + m + 1` given by
`a₀ -r→ a₁ -r→ ... -r→ aₙ -r→ b₀ -r→ b₁ -r→ ... -r→ bₘ`.
-/
@[simps]
/-
**RelSeries.append** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：append (p q : RelSeries r) (connect : p.last ~[r] q.head) : RelSeries r wh
ere length
参数：p q : RelSeries r；connect : p.last ~[r] q.head。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a₀ -r→ a₁ -r→ ... -r→ aₙ` and `b₀ -r→ b₁ -r→ ... -r→ bₘ` are two strict seri
es
such that `r aₙ b₀`, then there is a chain of length `n + m + 1` given by
`a₀ -r→ a₁ -r→ ... -r→ aₙ -r→ b₀ -r→ b₁ -r→ ... -r→ bₘ`.
-/
def append (p q : RelSeries r) (connect : p.last ~[r] q.head) : RelSeries r where
  length := p.length + q.length + 1
  toFun := Fin.append p q ∘ Fin.cast (by lia)
  step i := by
    obtain hi | rfl | hi :=
      lt_trichotomy i (Fin.castLE (by lia) (Fin.last _ : Fin (p.length + 1)))
    · convert! p.step ⟨i.1, hi⟩ <;> convert! Fin.append_left p q _ <;> rfl
    · convert! connect
      · convert! Fin.append_left p q _
      · convert! Fin.append_right p q _; rfl
    · set x := _; set y := _
      change Fin.append p q x ~[r] Fin.append p q y
      have hx : x = Fin.natAdd _ ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi <|
          i.2.trans <| by lia⟩ := by
        ext; dsimp [x, y]; rw [Nat.add_sub_cancel']; exact hi
      have hy : y = Fin.natAdd _ ⟨i - p.length, Nat.sub_lt_left_of_lt_add (le_of_lt hi)
          (by exact i.2)⟩ := by
        ext
        dsimp
        conv_rhs => rw [Nat.add_comm p.length 1, add_assoc,
          Nat.add_sub_cancel' <| le_of_lt (show p.length < i.1 from hi), add_comm]
        rfl
      rw [hx, Fin.append_right, hy, Fin.append_right]
      convert! q.step ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi <| by lia⟩
      rw [Fin.succ_mk, Nat.sub_eq_iff_eq_add (le_of_lt hi : p.length ≤ i),
        Nat.add_assoc _ 1, add_comm 1, Nat.sub_add_cancel]
      exact hi

set_option backward.defeqAttrib.useBackward true in
/-
**RelSeries.append_apply_left** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：append_apply_left (p q : RelSeries r) (connect : p.last ~[r] q.head) (i : 
Fin (p.length + 1)) : p.append q connect ((i.castAdd (q.length + 1)).cast (by ds
imp; lia) : Fin ((p.append q connect).length + 1)) = p i
参数：p q : RelSeries r；connect : p.last ~[r] q.head；i : Fin (p.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Fin.append_left`：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin 
m) : append u v (Fin.castAdd n i) = u i
-/
lemma append_apply_left (p q : RelSeries r) (connect : p.last ~[r] q.head)
    (i : Fin (p.length + 1)) :
    p.append q connect
      ((i.castAdd (q.length + 1)).cast (by dsimp; lia) : Fin ((p.append q connect).length + 1))
        = p i := by
  delta append
  simp only [Function.comp_apply]
  convert! Fin.append_left _ _ _

set_option backward.defeqAttrib.useBackward true in
/-
**RelSeries.append_apply_right** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：append_apply_right (p q : RelSeries r) (connect : p.last ~[r] q.head) (i :
 Fin (q.length + 1)) : p.append q connect ((i.natAdd (p.length + 1)).cast (by ds
imp; lia) : Fin ((p.append q connect).length + 1)) = q i
参数：p q : RelSeries r；connect : p.last ~[r] q.head；i : Fin (q.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.append_right`：append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fi
n n) : append u v (natAdd m i) = v i
-/
lemma append_apply_right (p q : RelSeries r) (connect : p.last ~[r] q.head)
    (i : Fin (q.length + 1)) :
    p.append q connect
      ((i.natAdd (p.length + 1)).cast (by dsimp; lia) : Fin ((p.append q connect).length + 1))
        = q i :=
  Fin.append_right _ _ _
/-
**RelSeries.head_append** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p q : RelSeries r) (connect : (p.last, 
q.head) ∈ r),   (p.append q connect).head = p.head
参数：p q : RelSeries r；connect : (p.last, q.head) ∈ r；p.append q connect。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.append_apply_left`：append_apply_left (p q : RelSeries r) (conn
ect : p.last ~[r] q.head) (i : Fin (p.length + 1)) : p.append q connect ((i.cast
Add (q.length + 1…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma head_append (p q : RelSeries r) (connect : p.last ~[r] q.head) :
    (p.append q connect).head = p.head :=
  append_apply_left p q connect 0

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**RelSeries.last_append** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p q : RelSeries r) (connect : (p.last, 
q.head) ∈ r),   (p.append q connect).last = q.last
参数：p q : RelSeries r；connect : (p.last, q.head) ∈ r；p.append q connect。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用引理 `RelSeries.append_apply_right`：append_apply_right (p q : RelSeries r) (co
nnect : p.last ~[r] q.head) (i : Fin (q.length + 1)) : p.append q connect ((i.na
tAdd (p.length + 1…
-/
@[simp] lemma last_append (p q : RelSeries r) (connect : p.last ~[r] q.head) :
    (p.append q connect).last = q.last := by
  delta last
  convert! append_apply_right p q connect (Fin.last _)
  ext1
  dsimp
  lia

set_option backward.isDefEq.respectTransparency false in
/-
**RelSeries.append_assoc** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：append_assoc (p q w : RelSeries r) (hpq : p.last ~[r] q.head) (hqw : q.las
t ~[r] w.head) : (p.append q hpq).append w (by simpa) = p.append (q.append w hqw
) (by simpa)
参数：p q w : RelSeries r；hpq : p.last ~[r] q.head；hqw : q.last ~[r] w.head。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.ext`：ext {x y : RelSeries r} (length_eq : x.length = y.length)
 (toFun_eq : x.toFun = y.toFun ∘ Fin.cast (by rw [length_eq])) : x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.append_length`：∀ {α : Type u_1} {r : SetRel α α} (p q : RelSer
ies r) (connect : (p.last, q.head) ∈ r),   (p.append q connect).length = p.lengt
h + q.length …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Fin.append_cast_left`：∀ {α : Sort u_1} {n m : ℕ} (xs : Fin n → α) (ys : 
Fin m → α) (n' : ℕ) (h : n' = n),   Fin.append (xs ∘ Fin.cast h) ys = Fin.append
 xs ys ∘ F…
· 使用定理 `Fin.append_assoc`：append_assoc {p : Nat} (a : Fin m -> α) (b : Fin n -> 
α) (c : Fin p -> α) : append (append a b) c = append a (append b c) ∘ Fin.cast (
Nat.ad…
· 使用定理 `Fin.append_cast_right`：∀ {α : Sort u_1} {n m : ℕ} (xs : Fin n → α) (ys :
 Fin m → α) (m' : ℕ) (h : m' = m),   Fin.append xs (ys ∘ Fin.cast h) = Fin.appen
d xs ys ∘ F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma append_assoc (p q w : RelSeries r) (hpq : p.last ~[r] q.head) (hqw : q.last ~[r] w.head) :
    (p.append q hpq).append w (by simpa) = p.append (q.append w hqw) (by simpa) := by
  ext
  · simp only [append_length, Nat.add_left_inj]
    lia
  · simp [append, Fin.append_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**RelSeries.toList_append** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：toList_append (p q : RelSeries r) (connect : p.last ~[r] q.head) : (p.appe
nd q connect).toList = p.toList ++ q.toList
参数：p q : RelSeries r；connect : p.last ~[r] q.head。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem`：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁
.length l₂.length, l₁[n]? = l₂[n]?) : l₁ = l₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RelSeries.length_toList`：length_toList (x : RelSeries r) : x.toList.leng
th = x.length + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Nat.sub_lt_right_of_lt_add`：∀ {n k m : ℕ}, n ≤ k → k < m + n → k - n < m
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用引理 `RelSeries.toList_getElem`：toList_getElem (p : RelSeries r) {i : Nat} (hi
 : i < p.toList.length) : p.toList[(i : Nat)] = p ⟨i, by simpa using hi⟩
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Fin.castAdd_castLT`：∀ {n : ℕ} (m : ℕ) (i : Fin (n + m)) (hi : ↑i < n), F
in.castAdd m (i.castLT hi) = i
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `List.getElem_append`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ} (h : i < 
(l₁ ++ l₂).length),   (l₁ ++ l₂)[i] = if h' : i < l₁.length then l₁[i] else l₂[i
 - l₁.len…
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma toList_append (p q : RelSeries r) (connect : p.last ~[r] q.head) :
    (p.append q connect).toList = p.toList ++ q.toList := by
  apply List.ext_getElem
  · simp; grind
  · simp [List.getElem_append, Fin.append, Fin.addCases]
/--
For two types `α, β` and relation on them `r, s`, if `f : α → β` preserves relation `r`, then an
`r`-series can be pushed out to an `s`-series by
`a₀ -r→ a₁ -r→ ... -r→ aₙ ↦ f a₀ -s→ f a₁ -s→ ... -s→ f aₙ`
-/
@[simps length]
/-
**RelSeries.map** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：map (p : RelSeries r) (f : r.Hom s) : RelSeries s where length
参数：p : RelSeries r；f : r.Hom s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For two types `α, β` and relation on them `r, s`, if `f : α → β` preserves relat
ion `r`, then an
`r`-series can be pushed out to an `s`-series by
`a₀ -r→ a₁ -r→ ... -r→ aₙ ↦ f a₀ -s→ f a₁ -s→ ... -s→ f aₙ`
-/
def map (p : RelSeries r) (f : r.Hom s) : RelSeries s where
  length := p.length
  toFun := f.1.comp p
  step := (f.2 <| p.step ·)
/-
**RelSeries.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} {β : Type u_2} {s : SetRel β β} (p : Rel
Series r) (f : r.Hom s)   (i : Fin (p.length + 1)), (p.map f).toFun i = f (p.toF
un i)
参数：p : RelSeries r；f : r.Hom s；i : Fin (p.length + 1)；p.map f；p.toFun i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_apply (p : RelSeries r) (f : r.Hom s) (i : Fin (p.length + 1)) :
    p.map f i = f (p i) := rfl
/-
**RelSeries.head_map** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} {β : Type u_2} {s : SetRel β β} (p : Rel
Series r) (f : r.Hom s),   (p.map f).head = f p.head
参数：p : RelSeries r；f : r.Hom s；p.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma head_map (p : RelSeries r) (f : r.Hom s) : (p.map f).head = f p.head := rfl
/-
**RelSeries.last_map** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} {β : Type u_2} {s : SetRel β β} (p : Rel
Series r) (f : r.Hom s),   (p.map f).last = f p.last
参数：p : RelSeries r；f : r.Hom s；p.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma last_map (p : RelSeries r) (f : r.Hom s) : (p.map f).last = f p.last := rfl

set_option backward.isDefEq.respectTransparency false in
/--
If `a₀ -r→ a₁ -r→ ... -r→ aₙ` is an `r`-series and `a` is such that
`aᵢ -r→ a -r→ a_ᵢ₊₁`, then
`a₀ -r→ a₁ -r→ ... -r→ aᵢ -r→ a -r→ aᵢ₊₁ -r→ ... -r→ aₙ`
is another `r`-series
-/
@[simps]
/-
**RelSeries.insertNth** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：insertNth (p : RelSeries r) (i : Fin p.length) (a : α) (prev_connect : p (
Fin.castSucc i) ~[r] a) (connect_next : a ~[r] p i.succ) : RelSeries r where len
gth
参数：p : RelSeries r；i : Fin p.length；a : α；prev_connect : p (Fin.castSucc i) ~[r]
 a；connect_next : a ~[r] p i.succ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a₀ -r→ a₁ -r→ ... -r→ aₙ` is an `r`-series and `a` is such that
`aᵢ -r→ a -r→ a_ᵢ₊₁`, then
`a₀ -r→ a₁ -r→ ... -r→ aᵢ -r→ a -r→ aᵢ₊₁ -r→ ... -r→ aₙ`
is another `r`-series
-/
def insertNth (p : RelSeries r) (i : Fin p.length) (a : α)
    (prev_connect : p (Fin.castSucc i) ~[r] a) (connect_next : a ~[r] p i.succ) : RelSeries r where
  length := p.length + 1
  toFun := (Fin.castSucc i.succ).insertNth a p
  step m := by
    set x := _; set y := _; change x ~[r] y
    obtain hm | hm | hm := lt_trichotomy m.1 i.1
    · convert! p.step ⟨m, hm.trans i.2⟩
      · change Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · exact hm.trans (lt_add_one _)
        simp
      · change Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · change m.1 + 1 < i.1 + 1; rwa [add_lt_add_iff_right]
        simp; rfl
    · rw [show x = p m from show Fin.insertNth _ _ _ _ = _ by
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · change m.1 < i.1 + 1; exact hm ▸ lt_add_one _
        simp]
      convert! prev_connect
      · ext; exact hm
      · change Fin.insertNth _ _ _ _ = _
        rw [show m.succ = i.succ.castSucc by ext; change _ + 1 = _ + 1; rw [hm],
          Fin.insertNth_apply_same]
    · rw [Nat.lt_iff_add_one_le, le_iff_lt_or_eq] at hm
      obtain hm | hm := hm
      · convert! p.step ⟨m.1 - 1, Nat.sub_lt_right_of_lt_add (by lia) m.2⟩
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above (h := hm)]
          aesop
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap
          · exact hm.trans (lt_add_one _)
          simp only [Fin.pred_succ, eq_rec_constant, Fin.succ_mk]
          congr
          exact Fin.ext <| Eq.symm <| Nat.succ_pred_eq_of_pos (lt_trans (Nat.zero_lt_succ _) hm)
      · convert! connect_next
        · change Fin.insertNth _ _ _ _ = _
          rw [show m.castSucc = i.succ.castSucc from Fin.ext hm.symm, Fin.insertNth_apply_same]
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap
          · change i.1 + 1 < m.1 + 1; lia
          simp only [Fin.pred_succ, eq_rec_constant]
          congr; ext; exact hm.symm

/--
A relation series `a₀ -r→ a₁ -r→ ... -r→ aₙ` of `r` gives a relation series of the reverse of `r`
by reversing the series `aₙ ←r- aₙ₋₁ ←r- ... ←r- a₁ ←r- a₀`.
-/
@[simps length]
/-
**RelSeries.reverse** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：reverse (p : RelSeries r) : RelSeries r.inv where length
参数：p : RelSeries r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation series `a₀ -r→ a₁ -r→ ... -r→ aₙ` of `r` gives a relation series of t
he reverse of `r`
by reversing the series `aₙ ←r- aₙ₋₁ ←r- ... ←r- a₁ ←r- a₀`.
-/
def reverse (p : RelSeries r) : RelSeries r.inv where
  length := p.length
  toFun := p ∘ Fin.rev
  step i := by
    rw [Function.comp_apply, Function.comp_apply, SetRel.mem_inv]
    have hi : i.1 + 1 ≤ p.length := by lia
    convert! p.step ⟨p.length - (i.1 + 1), Nat.sub_lt_self (by lia) hi⟩
    · ext; simp
    · ext
      simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
      lia
/-
**RelSeries.reverse_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r) (i : Fin (p.length + 1
)), p.reverse.toFun i = p.toFun i.rev
参数：p : RelSeries r；i : Fin (p.length + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma reverse_apply (p : RelSeries r) (i : Fin (p.length + 1)) :
    p.reverse i = p i.rev := rfl

set_option backward.defeqAttrib.useBackward true in
/-
**RelSeries.last_reverse** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r), p.reverse.last = p.he
ad
参数：p : RelSeries r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.rev_last`：∀ (n : ℕ), (Fin.last n).rev = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma last_reverse (p : RelSeries r) : p.reverse.last = p.head := by
  simp [RelSeries.last, RelSeries.head]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**RelSeries.head_reverse** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r), p.reverse.head = p.la
st
参数：p : RelSeries r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.rev_zero`：∀ (n : ℕ), Fin.rev 0 = Fin.last n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma head_reverse (p : RelSeries r) : p.reverse.head = p.last := by
  simp [RelSeries.last, RelSeries.head]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**RelSeries.reverse_reverse** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r), p.reverse.reverse = p
参数：p : RelSeries r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.ext`：ext {x y : RelSeries r} (length_eq : x.length = y.length)
 (toFun_eq : x.toFun = y.toFun ∘ Fin.cast (by rw [length_eq])) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.cast_refl`：∀ (n : ℕ) (h : n = n), Fin.cast h = id
-/
@[simp] lemma reverse_reverse {r : SetRel α α} (p : RelSeries r) : p.reverse.reverse = p := by
  ext <;> simp

/--
Given a series `a₀ -r→ a₁ -r→ ... -r→ aₙ` and an `a` such that `a₀ -r→ a` holds, there is
a series of length `n+1`: `a -r→ a₀ -r→ a₁ -r→ ... -r→ aₙ`.
-/
@[simps! length]
/-
**RelSeries.cons** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：cons (p : RelSeries r) (newHead : α) (rel : newHead ~[r] p.head) : RelSeri
es r
参数：p : RelSeries r；newHead : α；rel : newHead ~[r] p.head。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a series `a₀ -r→ a₁ -r→ ... -r→ aₙ` and an `a` such that `a₀ -r→ a` holds,
 there is
a series of length `n+1`: `a -r→ a₀ -r→ a₁ -r→ ... -r→ aₙ`.
-/
def cons (p : RelSeries r) (newHead : α) (rel : newHead ~[r] p.head) : RelSeries r :=
  (singleton r newHead).append p rel
/-
**RelSeries.head_cons** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r) (newHead : α) (rel : (
newHead, p.head) ∈ r),   (p.cons newHead rel).head = newHead
参数：p : RelSeries r；newHead : α；rel : (newHead, p.head) ∈ r；p.cons newHead rel。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma head_cons (p : RelSeries r) (newHead : α) (rel : newHead ~[r] p.head) :
    (p.cons newHead rel).head = newHead := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**RelSeries.last_cons** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r) (newHead : α) (rel : (
newHead, p.head) ∈ r),   (p.cons newHead rel).last = p.last
参数：p : RelSeries r；newHead : α；rel : (newHead, p.head) ∈ r；p.cons newHead rel。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.last_append`：∀ {α : Type u_1} {r : SetRel α α} (p q : RelSerie
s r) (connect : (p.last, q.head) ∈ r),   (p.append q connect).last = q.last
-/
@[simp] lemma last_cons (p : RelSeries r) (newHead : α) (rel : newHead ~[r] p.head) :
    (p.cons newHead rel).last = p.last := by
  delta cons
  rw [last_append]

set_option backward.isDefEq.respectTransparency false in
/-
**RelSeries.cons_cast_succ** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：cons_cast_succ (s : RelSeries r) (a : α) (h : a ~[r] s.head) (i : Fin (s.l
ength + 1)) : (s.cons a h) (.cast (by simp) (.succ i)) = s i
参数：s : RelSeries r；a : α；h : a ~[r] s.head；i : Fin (s.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ.inj`：∀ {m n : ℕ}, m.succ = n.succ → m = n
· 使用定理 `RelSeries.append_toFun`：∀ {α : Type u_1} {r : SetRel α α} (p q : RelSeri
es r) (connect : (p.last, q.head) ∈ r)   (a : Fin (p.length + q.length + 1 + 1))
, (p.append …
· 使用定理 `Fin.castAdd_castLT`：∀ {n : ℕ} (m : ℕ) (i : Fin (n + m)) (hi : ↑i < n), F
in.castAdd m (i.castLT hi) = i
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `RelSeries.singleton_length`：∀ {α : Type u_1} (r : SetRel α α) (a : α), (
RelSeries.singleton r a).length = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cons_cast_succ (s : RelSeries r) (a : α) (h : a ~[r] s.head) (i : Fin (s.length + 1)) :
    (s.cons a h) (.cast (by simp) (.succ i)) = s i := by
  simp [cons, Fin.append, Fin.addCases, Fin.subNat]

@[simp]
/-
**RelSeries.append_singleton_left** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：append_singleton_left (p : RelSeries r) (x : α) (hx : x ~[r] p.head) : (si
ngleton r x).append p hx = p.cons x hx
参数：p : RelSeries r；x : α；hx : x ~[r] p.head。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma append_singleton_left (p : RelSeries r) (x : α) (hx : x ~[r] p.head) :
    (singleton r x).append p hx = p.cons x hx :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**RelSeries.toList_cons** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：toList_cons (p : RelSeries r) (x : α) (hx : x ~[r] p.head) : (p.cons x hx)
.toList = x :: p.toList
参数：p : RelSeries r；x : α；hx : x ~[r] p.head。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.cons.eq_1`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r)
 (newHead : α) (rel : (newHead, p.head) ∈ r),   p.cons newHead rel = (RelSeries.
singleton…
· 使用引理 `RelSeries.toList_append`：toList_append (p q : RelSeries r) (connect : p.
last ~[r] q.head) : (p.append q connect).toList = p.toList ++ q.toList
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RelSeries.toList_singleton`：toList_singleton (x : α) : (singleton r x).t
oList = [x]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toList_cons (p : RelSeries r) (x : α) (hx : x ~[r] p.head) :
    (p.cons x hx).toList = x :: p.toList := by
  rw [cons, toList_append]
  simp
/-
**RelSeries.fromListIsChain_cons** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：fromListIsChain_cons (l : List α) (l_ne_nil : l != []) (hl : l.IsChain (· 
~[r] ·)) (x : α) (hx : x ~[r] l.head l_ne_nil) : fromListIsChain (x :: l) (by si
mp) (hl.cons_of_ne_nil l_ne_nil hx) = (fromListIsChain l l_ne_nil hl).cons x (by
 simpa)
参数：l : List α；l_ne_nil : l != []；hl : l.IsChain (· ~[r] ·)；x : α；hx : x ~[r] l.h
ead l_ne_nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用引理 `RelSeries.toList_injective`：toList_injective : Function.Injective (RelSe
ries.toList (r
· 使用定理 `List.IsChain.cons_of_ne_nil`：∀ {α : Type u_1} {R : α → α → Prop} {x : α}
 {l : List α} (l_ne_nil : l ≠ []),   List.IsChain R l → R x (l.head l_ne_nil) → 
List.IsChain R (x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RelSeries.toList_fromListIsChain`：toList_fromListIsChain (l : List α) (l
_ne_nil : l != []) (hl : l.IsChain (· ~[r] ·)) : (fromListIsChain l l_ne_nil hl)
.toList = l
· 使用引理 `RelSeries.toList_cons`：toList_cons (p : RelSeries r) (x : α) (hx : x ~[r
] p.head) : (p.cons x hx).toList = x :: p.toList
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromListIsChain_cons (l : List α) (l_ne_nil : l ≠ [])
    (hl : l.IsChain (· ~[r] ·)) (x : α) (hx : x ~[r] l.head l_ne_nil) :
    fromListIsChain (x :: l) (by simp) (hl.cons_of_ne_nil l_ne_nil hx) =
      (fromListIsChain l l_ne_nil hl).cons x (by simpa) := by
  apply toList_injective
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**RelSeries.append_cons** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：append_cons {p q : RelSeries r} {x : α} (hx : x ~[r] p.head) (hq : p.last 
~[r] q.head) : (p.cons x hx).append q (by simpa) = (p.append q hq).cons x (by si
mpa)
参数：hx : x ~[r] p.head；hq : p.last ~[r] q.head。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RelSeries.append_assoc`：append_assoc (p q w : RelSeries r) (hpq : p.last
 ~[r] q.head) (hqw : q.last ~[r] w.head) : (p.append q hpq).append w (by simpa) 
= p.append (…
-/
lemma append_cons {p q : RelSeries r} {x : α} (hx : x ~[r] p.head) (hq : p.last ~[r] q.head) :
    (p.cons x hx).append q (by simpa) = (p.append q hq).cons x (by simpa) := by
  simp only [cons]
  rw [append_assoc]

/--
Given a series `a₀ -r→ a₁ -r→ ... -r→ aₙ` and an `a` such that `aₙ -r→ a` holds, there is
a series of length `n+1`: `a₀ -r→ a₁ -r→ ... -r→ aₙ -r→ a`.
-/
@[simps! length]
/-
**RelSeries.snoc** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：snoc (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast) : RelSeri
es r
参数：p : RelSeries r；newLast : α；rel : p.last ~[r] newLast。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a series `a₀ -r→ a₁ -r→ ... -r→ aₙ` and an `a` such that `aₙ -r→ a` holds,
 there is
a series of length `n+1`: `a₀ -r→ a₁ -r→ ... -r→ aₙ -r→ a`.
-/
def snoc (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast) : RelSeries r :=
  p.append (singleton r newLast) rel

set_option backward.isDefEq.respectTransparency false in
/-
**RelSeries.head_snoc** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r) (newLast : α) (rel : (
p.last, newLast) ∈ r),   (p.snoc newLast rel).head = p.head
参数：p : RelSeries r；newLast : α；rel : (p.last, newLast) ∈ r；p.snoc newLast rel。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelSeries.head_append`：∀ {α : Type u_1} {r : SetRel α α} (p q : RelSerie
s r) (connect : (p.last, q.head) ∈ r),   (p.append q connect).head = p.head
-/
@[simp] lemma head_snoc (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast) :
    (p.snoc newLast rel).head = p.head := by
  delta snoc; rw [head_append]
/-
**RelSeries.last_snoc** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r) (newLast : α) (rel : (
p.last, newLast) ∈ r),   (p.snoc newLast rel).last = newLast
参数：p : RelSeries r；newLast : α；rel : (p.last, newLast) ∈ r；p.snoc newLast rel。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelSeries.last_append`：∀ {α : Type u_1} {r : SetRel α α} (p q : RelSerie
s r) (connect : (p.last, q.head) ∈ r),   (p.append q connect).last = q.last
-/
@[simp] lemma last_snoc (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast) :
    (p.snoc newLast rel).last = newLast := last_append _ _ _
/-
**RelSeries.snoc_cast_castSucc** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：snoc_cast_castSucc (s : RelSeries r) (a : α) (h : s.last ~[r] a) (i : Fin 
(s.length + 1)) : (s.snoc a h) (.cast (by simp) (.castSucc i)) = s i
参数：s : RelSeries r；a : α；h : s.last ~[r] a；i : Fin (s.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.append_apply_left`：append_apply_left (p q : RelSeries r) (conn
ect : p.last ~[r] q.head) (i : Fin (p.length + 1)) : p.append q connect ((i.cast
Add (q.length + 1…
-/
lemma snoc_cast_castSucc (s : RelSeries r) (a : α) (h : s.last ~[r] a) (i : Fin (s.length + 1)) :
    (s.snoc a h) (.cast (by simp) (.castSucc i)) = s i :=
  append_apply_left s (singleton r a) h i

-- This lemma is useful because `last_snoc` is about `Fin.last (p.snoc _ _).length`, but we often
-- see `Fin.last (p.length + 1)` in practice. They are equal by definition, but sometimes simplifier
-- does not pick up `last_snoc`
/-
**RelSeries.last_snoc'** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r) (newLast : α) (rel : (
p.last, newLast) ∈ r),   (p.snoc newLast rel).toFun (Fin.last (p.length + 1)) = 
newLast
参数：p : RelSeries r；newLast : α；rel : (p.last, newLast) ∈ r；p.snoc newLast rel；Fi
n.last (p.length + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelSeries.last_append`：∀ {α : Type u_1} {r : SetRel α α} (p q : RelSerie
s r) (connect : (p.last, q.head) ∈ r),   (p.append q connect).last = q.last
-/
@[simp] lemma last_snoc' (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast) :
    p.snoc newLast rel (Fin.last (p.length + 1)) = newLast := last_append _ _ _
/-
**RelSeries.snoc_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (s : RelSeries r) (a : α) (connect : (s.
last, a) ∈ r) (i : Fin (s.length + 1)),   (s.snoc a connect).toFun i.castSucc = 
s.toFun i
参数：s : RelSeries r；a : α；connect : (s.last, a) ∈ r；i : Fin (s.length + 1)；s.snoc
 a connect。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.append_left`：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin 
m) : append u v (Fin.castAdd n i) = u i
-/
@[simp] lemma snoc_castSucc (s : RelSeries r) (a : α) (connect : s.last ~[r] a)
    (i : Fin (s.length + 1)) : snoc s a connect (Fin.castSucc i) = s i :=
  Fin.append_left _ _ i

set_option backward.isDefEq.respectTransparency false in
/-
**RelSeries.mem_snoc** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：mem_snoc {p : RelSeries r} {newLast : α} {rel : p.last ~[r] newLast} {x : 
α} : x in p.snoc newLast rel ↔ x in p ∨ x = newLast
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.append_right`：append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fi
n n) : append u v (natAdd m i) = v i
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.append_left`：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin 
m) : append u v (Fin.castAdd n i) = u i
-/
lemma mem_snoc {p : RelSeries r} {newLast : α} {rel : p.last ~[r] newLast} {x : α} :
    x ∈ p.snoc newLast rel ↔ x ∈ p ∨ x = newLast := by
  simp only [snoc, append, mem_def, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact Fin.lastCases (Or.inr <| Fin.append_right _ _ 0) (fun i => Or.inl ⟨⟨i.1, i.2⟩,
      (Fin.append_left _ _ _).symm⟩) i
  · intro h
    rcases h with (⟨i, rfl⟩ | rfl)
    · exact ⟨i.castSucc, Fin.append_left _ _ _⟩
    · exact ⟨Fin.last _, Fin.append_right _ _ 0⟩

/--
If a series `a₀ -r→ a₁ -r→ ...` has positive length, then `a₁ -r→ ...` is another series
-/
@[simps]
/-
**RelSeries.tail** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：tail (p : RelSeries r) (len_pos : p.length != 0) : RelSeries r where lengt
h
参数：p : RelSeries r；len_pos : p.length != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a series `a₀ -r→ a₁ -r→ ...` has positive length, then `a₁ -r→ ...` is anothe
r series
-/
def tail (p : RelSeries r) (len_pos : p.length ≠ 0) : RelSeries r where
  length := p.length - 1
  toFun := Fin.tail p ∘ (Fin.cast <| Nat.succ_pred_eq_of_pos <| Nat.pos_of_ne_zero len_pos)
  step i := p.step ⟨i.1 + 1, Nat.lt_pred_iff.mp i.2⟩
/-
**RelSeries.head_tail** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r) (len_pos : p.length ≠ 
0), (p.tail len_pos).head = p.toFun 1
参数：p : RelSeries r；len_pos : p.length ≠ 0；p.tail len_pos。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
@[simp] lemma head_tail (p : RelSeries r) (len_pos : p.length ≠ 0) :
    (p.tail len_pos).head = p 1 := by
  change p (Fin.succ _) = p 1
  congr
  ext
  change (1 : ℕ) = (1 : ℕ) % _
  rw [Nat.mod_eq_of_lt]
  simpa only [lt_add_iff_pos_left, Nat.pos_iff_ne_zero]
/-
**RelSeries.last_tail** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r) (len_pos : p.length ≠ 
0), (p.tail len_pos).last = p.last
参数：p : RelSeries r；len_pos : p.length ≠ 0；p.tail len_pos。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
-/
@[simp] lemma last_tail (p : RelSeries r) (len_pos : p.length ≠ 0) :
    (p.tail len_pos).last = p.last := by
  change p _ = p _
  congr
  ext
  simp only [Fin.val_succ, Fin.val_last]
  exact Nat.succ_pred_eq_of_pos (by simpa [Nat.pos_iff_ne_zero] using len_pos)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**RelSeries.toList_tail** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：toList_tail {p : RelSeries r} (hp : p.length != 0) : (p.tail hp).toList = 
p.toList.tail
参数：hp : p.length != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem`：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁
.length l₂.length, l₁[n]? = l₂[n]?) : l₁ = l₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RelSeries.length_toList`：length_toList (x : RelSeries r) : x.toList.leng
th = x.length + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_tail`：∀ {α : Type u_1} {l : List α}, l.tail.length = l.lengt
h - 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Nat.add_lt_of_lt_sub`：∀ {a b c : ℕ}, a < c - b → a + b < c
· 使用引理 `RelSeries.toList_getElem`：toList_getElem (p : RelSeries r) {i : Nat} (hi
 : i < p.toList.length) : p.toList[(i : Nat)] = p ⟨i, by simpa using hi⟩
· 使用定理 `List.getElem_tail`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i < l.tail
.length), l.tail[i] = l[i + 1]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toList_tail {p : RelSeries r} (hp : p.length ≠ 0) : (p.tail hp).toList = p.toList.tail := by
  refine List.ext_getElem ?_ fun i h1 h2 ↦ ?_
  · simp
    lia
  · simp [Fin.tail]

@[simp]
/-
**RelSeries.tail_cons** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：tail_cons (p : RelSeries r) (x : α) (hx : x ~[r] p.head) : (p.cons x hx).t
ail (by simp) = p
参数：p : RelSeries r；x : α；hx : x ~[r] p.head。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.toList_injective`：toList_injective : Function.Injective (RelSe
ries.toList (r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RelSeries.toList_tail`：toList_tail {p : RelSeries r} (hp : p.length != 0
) : (p.tail hp).toList = p.toList.tail
· 使用引理 `RelSeries.toList_cons`：toList_cons (p : RelSeries r) (x : α) (hx : x ~[r
] p.head) : (p.cons x hx).toList = x :: p.toList
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tail_cons (p : RelSeries r) (x : α) (hx : x ~[r] p.head) :
    (p.cons x hx).tail (by simp) = p := by
  apply toList_injective
  simp
/-
**RelSeries.cons_self_tail** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：cons_self_tail {p : RelSeries r} (hp : p.length != 0) : (p.tail hp).cons p
.head (p.3 ⟨0, Nat.zero_lt_of_ne_zero hp⟩) = p
参数：hp : p.length != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.toList_injective`：toList_injective : Function.Injective (RelSe
ries.toList (r
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用引理 `RelSeries.toList_ne_nil`：toList_ne_nil (x : RelSeries r) : x.toList != [
]
· 使用定理 `RelSeries.cons.congr_simp`：∀ {α : Type u_1} {r : SetRel α α} (p p_1 : Re
lSeries r) (e_p : p = p_1) (newHead newHead_1 : α)   (e_newHead : newHead = newH
ead_1) (rel : (…
· 使用引理 `RelSeries.toList_cons`：toList_cons (p : RelSeries r) (x : α) (hx : x ~[r
] p.head) : (p.cons x hx).toList = x :: p.toList
· 使用引理 `RelSeries.toList_tail`：toList_tail {p : RelSeries r} (hp : p.length != 0
) : (p.tail hp).toList = p.toList.tail
· 使用定理 `List.cons_head_tail`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head 
h :: l.tail = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cons_self_tail {p : RelSeries r} (hp : p.length ≠ 0) :
    (p.tail hp).cons p.head (p.3 ⟨0, Nat.zero_lt_of_ne_zero hp⟩) = p := by
  apply toList_injective
  simp [← head_toList]

set_option backward.isDefEq.respectTransparency false in
/--
To show a proposition `p` for `xs : RelSeries r` it suffices to show it for all singletons
and to show that when `p` holds for `xs` it also holds for `xs` prepended with one element.

Note: This can also be used to construct data, but it does not have good definitional properties,
since `(p.cons x hx).tail _ = p` is not a definitional equality.
-/
@[elab_as_elim]
/-
**RelSeries.inductionOn** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：inductionOn (motive : RelSeries r -> Sort*) (singleton : (x : α) -> motive
 (RelSeries.singleton r x)) (cons : (p : RelSeries r) -> (x : α) -> (hx : x ~[r]
 p.head) -> (hp : motive p) -> motive (p.cons x hx)) (p : RelSeries r) : motive 
p
参数：motive : RelSeries r -> Sort*；singleton : (x : α) -> motive (RelSeries.single
ton r x)；cons : (p : RelSeries r) -> (x : α) -> (hx : x ~[r] p.head) -> (hp : mo
tive p) -> motive (p.cons x hx)；p : RelSeries r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show a proposition `p` for `xs : RelSeries r` it suffices to show it for all 
singletons
and to show that when `p` holds for `xs` it also holds for `xs` prepended with o
ne element.

Note: This can also be used to construct data, but it does not have good definit
ional properties,
since `(p.cons x hx).tail _ = p` is not a definitional equality.
-/
def inductionOn (motive : RelSeries r → Sort*)
    (singleton : (x : α) → motive (RelSeries.singleton r x))
    (cons : (p : RelSeries r) → (x : α) → (hx : x ~[r] p.head) → (hp : motive p) →
      motive (p.cons x hx)) (p : RelSeries r) :
    motive p := by
  let {n : ℕ} (heq : p.length = n) : motive p := by
    induction n generalizing p with
    | zero =>
      convert! singleton p.head
      ext n
      · exact heq
      simp [show n = 0 by lia, apply_zero]
    | succ d hd =>
      have lq := p.tail_length (heq ▸ d.zero_ne_add_one.symm)
      nth_rw 3 [heq] at lq
      convert!
        cons (p.tail (heq ▸ d.zero_ne_add_one.symm)) p.head (p.3 ⟨0, heq ▸ d.zero_lt_succ⟩)
          (hd _ lq)
      exact (p.cons_self_tail (heq ▸ d.zero_ne_add_one.symm)).symm
  exact this rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**RelSeries.toList_snoc** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：toList_snoc (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast) : 
(p.snoc newLast rel).toList = p.toList ++ [newLast]
参数：p : RelSeries r；newLast : α；rel : p.last ~[r] newLast。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RelSeries.toList_append`：toList_append (p q : RelSeries r) (connect : p.
last ~[r] q.head) : (p.append q connect).toList = p.toList ++ q.toList
· 使用引理 `RelSeries.toList_singleton`：toList_singleton (x : α) : (singleton r x).t
oList = [x]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toList_snoc (p : RelSeries r) (newLast : α) (rel : p.last ~[r] newLast) :
    (p.snoc newLast rel).toList = p.toList ++ [newLast] := by
  simp [snoc]

/--
If a series ``a₀ -r→ a₁ -r→ ... -r→ aₙ``, then `a₀ -r→ a₁ -r→ ... -r→ aₙ₋₁` is
another series -/
@[simps]
/-
**RelSeries.eraseLast** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：eraseLast (p : RelSeries r) : RelSeries r where length
参数：p : RelSeries r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a series ``a₀ -r→ a₁ -r→ ... -r→ aₙ``, then `a₀ -r→ a₁ -r→ ... -r→ aₙ₋₁` is
another series
-/
def eraseLast (p : RelSeries r) : RelSeries r where
  length := p.length - 1
  toFun i := p ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ (Nat.sub_le _ _))⟩
  step i := p.step ⟨i, lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩
/-
**RelSeries.head_eraseLast** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r), p.eraseLast.head = p.
head
参数：p : RelSeries r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma head_eraseLast (p : RelSeries r) : p.eraseLast.head = p.head := rfl
/-
**RelSeries.last_eraseLast** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r), p.eraseLast.last = p.
toFun ⟨p.length.pred, ⋯⟩
参数：p : RelSeries r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma last_eraseLast (p : RelSeries r) :
    p.eraseLast.last = p ⟨p.length.pred, Nat.lt_succ_iff.2 (Nat.pred_le _)⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- In a non-trivial series `p`, the last element of `p.eraseLast` is related to `p.last` -/
/-
**RelSeries.eraseLast_last_rel_last** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：eraseLast_last_rel_last (p : RelSeries r) (h : p.length != 0) : p.eraseLas
t.last ~[r] p.last
参数：p : RelSeries r；h : p.length != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `RelSeries.eraseLast_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSe
ries r), p.eraseLast.length = p.length - 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `RelSeries.eraseLast_toFun`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSer
ies r) (i : Fin (p.length - 1 + 1)), p.eraseLast.toFun i = p.toFun ⟨↑i, ⋯⟩
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r

--- 原说明 ---
In a non-trivial series `p`, the last element of `p.eraseLast` is related to `p.
last`
-/
lemma eraseLast_last_rel_last (p : RelSeries r) (h : p.length ≠ 0) :
    p.eraseLast.last ~[r] p.last := by
  simp only [last, Fin.last, eraseLast_length, eraseLast_toFun]
  convert! p.step ⟨p.length - 1, by lia⟩
  simp only [Fin.succ_mk]; lia

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**RelSeries.toList_eraseLast** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：toList_eraseLast (p : RelSeries r) (hp : p.length != 0) : p.eraseLast.toLi
st = p.toList.dropLast
参数：p : RelSeries r；hp : p.length != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem`：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁
.length l₂.length, l₁[n]? = l₂[n]?) : l₁ = l₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RelSeries.length_toList`：length_toList (x : RelSeries r) : x.toList.leng
th = x.length + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RelSeries.eraseLast_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSe
ries r), p.eraseLast.length = p.length - 1
· 使用定理 `List.length_dropLast`：∀ {α : Type u_1} {xs : List α}, xs.dropLast.length
 = xs.length - 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.succ_pred_eq_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → n.pred.succ = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RelSeries.toList_getElem`：toList_getElem (p : RelSeries r) {i : Nat} (hi
 : i < p.toList.length) : p.toList[(i : Nat)] = p ⟨i, by simpa using hi⟩
· 使用定理 `RelSeries.eraseLast_toFun`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSer
ies r) (i : Fin (p.length - 1 + 1)), p.eraseLast.toFun i = p.toFun ⟨↑i, ⋯⟩
· 使用定理 `List.getElem_dropLast`：∀ {α : Type u_1} {xs : List α} {i : ℕ} (h : i < x
s.dropLast.length), xs.dropLast[i] = xs[i]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toList_eraseLast (p : RelSeries r) (hp : p.length ≠ 0) :
    p.eraseLast.toList = p.toList.dropLast := by
  apply List.ext_getElem
  · simpa using Nat.succ_pred_eq_of_ne_zero hp
  · intro i hi h2
    simp
/-
**RelSeries.snoc_self_eraseLast** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：snoc_self_eraseLast (p : RelSeries r) (h : p.length != 0) : p.eraseLast.sn
oc p.last (p.eraseLast_last_rel_last h) = p
参数：p : RelSeries r；h : p.length != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.toList_injective`：toList_injective : Function.Injective (RelSe
ries.toList (r
· 使用引理 `RelSeries.eraseLast_last_rel_last`：eraseLast_last_rel_last (p : RelSerie
s r) (h : p.length != 0) : p.eraseLast.last ~[r] p.last
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RelSeries.toList_snoc`：toList_snoc (p : RelSeries r) (newLast : α) (rel 
: p.last ~[r] newLast) : (p.snoc newLast rel).toList = p.toList ++ [newLast]
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RelSeries.getLast_toList`：getLast_toList (p : RelSeries r) : p.toList.ge
tLast (by simp [toList]) = p.last
· 使用引理 `RelSeries.toList_eraseLast`：toList_eraseLast (p : RelSeries r) (hp : p.l
ength != 0) : p.eraseLast.toList = p.toList.dropLast
· 使用定理 `List.dropLast_append_getLast`：∀ {α : Type u} {l : List α} (h : l ≠ []), 
l.dropLast ++ [l.getLast h] = l
-/
lemma snoc_self_eraseLast (p : RelSeries r) (h : p.length ≠ 0) :
    p.eraseLast.snoc p.last (p.eraseLast_last_rel_last h) = p := by
  apply toList_injective
  rw [toList_snoc, ← getLast_toList, toList_eraseLast _ h, List.dropLast_append_getLast]

set_option backward.isDefEq.respectTransparency false in
/--
To show a proposition `p` for `xs : RelSeries r` it suffices to show it for all singletons
and to show that when `p` holds for `xs` it also holds for `xs` appended with one element.
-/
@[elab_as_elim]
/-
**RelSeries.inductionOn'** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：inductionOn' (motive : RelSeries r -> Sort*) (singleton : (x : α) -> motiv
e (RelSeries.singleton r x)) (snoc : (p : RelSeries r) -> (x : α) -> (hx : p.las
t ~[r] x) -> (hp : motive p) -> motive (p.snoc x hx)) (p : RelSeries r) : motive
 p
参数：motive : RelSeries r -> Sort*；singleton : (x : α) -> motive (RelSeries.single
ton r x)；snoc : (p : RelSeries r) -> (x : α) -> (hx : p.last ~[r] x) -> (hp : mo
tive p) -> motive (p.snoc x hx)；p : RelSeries r。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.eraseLast_last_rel_last`：eraseLast_last_rel_last (p : RelSerie
s r) (h : p.length != 0) : p.eraseLast.last ~[r] p.last

--- 原说明 ---
To show a proposition `p` for `xs : RelSeries r` it suffices to show it for all 
singletons
and to show that when `p` holds for `xs` it also holds for `xs` appended with on
e element.
-/
def inductionOn' (motive : RelSeries r → Sort*)
    (singleton : (x : α) → motive (RelSeries.singleton r x))
    (snoc : (p : RelSeries r) → (x : α) → (hx : p.last ~[r] x) → (hp : motive p) →
      motive (p.snoc x hx)) (p : RelSeries r) :
    motive p := by
  let {n : ℕ} (heq : p.length = n) : motive p := by
    induction n generalizing p with
    | zero =>
      convert! singleton p.head
      ext n
      · exact heq
      · simp [show n = 0 by lia, apply_zero]
    | succ d hd =>
      have ne0 : p.length ≠ 0 := by simp [heq]
      have len : p.eraseLast.length = d := by simp [heq]
      convert! snoc p.eraseLast p.last (p.eraseLast_last_rel_last ne0) (hd _ len)
      exact (p.snoc_self_eraseLast ne0).symm
  exact this rfl

/--
Given two series of the form `a₀ -r→ ... -r→ X` and `X -r→ b ---> ...`,
then `a₀ -r→ ... -r→ X -r→ b ...` is another series obtained by combining the given two.
-/
@[simps length]
/-
**RelSeries.smash** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：smash (p q : RelSeries r) (connect : p.last = q.head) : RelSeries r where 
length
参数：p q : RelSeries r；connect : p.last = q.head。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two series of the form `a₀ -r→ ... -r→ X` and `X -r→ b ---> ...`,
then `a₀ -r→ ... -r→ X -r→ b ...` is another series obtained by combining the gi
ven two.
-/
def smash (p q : RelSeries r) (connect : p.last = q.head) : RelSeries r where
  length := p.length + q.length
  toFun := Fin.addCases (m := p.length) (n := q.length + 1) (p ∘ Fin.castSucc) q
  step := by
    apply Fin.addCases <;> intro i
    · simp_rw [Fin.castSucc_castAdd, Fin.addCases_left, Fin.succ_castAdd]
      convert! p.step i
      split_ifs with h
      · rw [Fin.addCases_right, h, ← last, connect, head]
      · apply Fin.addCases_left
    simpa only [Fin.castSucc_natAdd, Fin.succ_natAdd, Fin.addCases_right] using q.step i
/-
**RelSeries.smash_castLE** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：smash_castLE {p q : RelSeries r} (h : p.last = q.head) (i : Fin (p.length 
+ 1)) : p.smash q h (i.castLE (by simp)) = p i
参数：h : p.last = q.head；i : Fin (p.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
-/
lemma smash_castLE {p q : RelSeries r} (h : p.last = q.head) (i : Fin (p.length + 1)) :
    p.smash q h (i.castLE (by simp)) = p i := by
  refine i.lastCases ?_ fun _ ↦ by dsimp only [smash]; apply Fin.addCases_left
  change p.smash q h (Fin.natAdd p.length (0 : Fin (q.length + 1))) = _
  simpa only [smash, Fin.addCases_right] using! h.symm
/-
**RelSeries.smash_castAdd** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：smash_castAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin p.length)
 : p.smash q h (i.castAdd q.length).castSucc = p i.castSucc
参数：h : p.last = q.head；i : Fin p.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.smash_castLE`：smash_castLE {p q : RelSeries r} (h : p.last = q
.head) (i : Fin (p.length + 1)) : p.smash q h (i.castLE (by simp)) = p i
-/
lemma smash_castAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin p.length) :
    p.smash q h (i.castAdd q.length).castSucc = p i.castSucc :=
  smash_castLE h i.castSucc
/-
**RelSeries.smash_succ_castAdd** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：smash_succ_castAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin p.le
ngth) : p.smash q h (i.castAdd q.length).succ = p i.succ
参数：h : p.last = q.head；i : Fin p.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.smash_castLE`：smash_castLE {p q : RelSeries r} (h : p.last = q
.head) (i : Fin (p.length + 1)) : p.smash q h (i.castLE (by simp)) = p i
-/
lemma smash_succ_castAdd {p q : RelSeries r} (h : p.last = q.head)
    (i : Fin p.length) : p.smash q h (i.castAdd q.length).succ = p i.succ :=
  smash_castLE h i.succ
/-
**RelSeries.smash_natAdd** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：smash_natAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin q.length) 
: smash p q h (i.natAdd p.length).castSucc = q i.castSucc
参数：h : p.last = q.head；i : Fin q.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
-/
lemma smash_natAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin q.length) :
    smash p q h (i.natAdd p.length).castSucc = q i.castSucc := by
  dsimp only [smash, Fin.castSucc_natAdd]
  apply Fin.addCases_right
/-
**RelSeries.smash_succ_natAdd** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：smash_succ_natAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin q.len
gth) : smash p q h (i.natAdd p.length).succ = q i.succ
参数：h : p.last = q.head；i : Fin q.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
-/
lemma smash_succ_natAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin q.length) :
    smash p q h (i.natAdd p.length).succ = q i.succ := by
  dsimp only [smash, Fin.succ_natAdd]
  apply Fin.addCases_right
/-
**RelSeries.head_smash** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} {p q : RelSeries r} (h : p.last = q.head
), (p.smash q h).head = p.head
参数：h : p.last = q.head；p.smash q h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma head_smash {p q : RelSeries r} (h : p.last = q.head) :
    (smash p q h).head = p.head := by
  obtain ⟨_ | _, _⟩ := p
  · simpa [Fin.addCases] using! h.symm
  dsimp only [smash, head]
  exact Fin.addCases_left 0
/-
**RelSeries.last_smash** 是 Mathlib 中的一个定理，位于命名空间 `RelSeries`。
形式化陈述：∀ {α : Type u_1} {r : SetRel α α} {p q : RelSeries r} (h : p.last = q.head
), (p.smash q h).last = q.last
参数：h : p.last = q.head；p.smash q h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.natAdd_last`：∀ {m n : ℕ}, Fin.natAdd n (Fin.last m) = Fin.last (n + 
m)
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
-/
@[simp] lemma last_smash {p q : RelSeries r} (h : p.last = q.head) :
    (smash p q h).last = q.last := by
  dsimp only [smash, last]
  rw [← Fin.natAdd_last, Fin.addCases_right]

/-- Given the series `a₀ -r→ … -r→ aᵢ -r→ … -r→ aₙ`, the series `a₀ -r→ … -r→ aᵢ`. -/
@[simps! length]
/-
**RelSeries.take** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：take {r : SetRel α α} (p : RelSeries r) (i : Fin (p.length + 1)) : RelSeri
es r where length
参数：p : RelSeries r；i : Fin (p.length + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the series `a₀ -r→ … -r→ aᵢ -r→ … -r→ aₙ`, the series `a₀ -r→ … -r→ aᵢ`.
-/
def take {r : SetRel α α} (p : RelSeries r) (i : Fin (p.length + 1)) : RelSeries r where
  length := i
  toFun := fun ⟨j, h⟩ => p.toFun ⟨j, by lia⟩
  step := fun ⟨j, h⟩ => p.step ⟨j, by lia⟩

@[simp]
/-
**RelSeries.head_take** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：head_take (p : RelSeries r) (i : Fin (p.length + 1)) : (p.take i).head = p
.head
参数：p : RelSeries r；i : Fin (p.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma head_take (p : RelSeries r) (i : Fin (p.length + 1)) :
    (p.take i).head = p.head := by simp [take, head]

@[simp]
/-
**RelSeries.last_take** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：last_take (p : RelSeries r) (i : Fin (p.length + 1)) : (p.take i).last = p
 i
参数：p : RelSeries r；i : Fin (p.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma last_take (p : RelSeries r) (i : Fin (p.length + 1)) :
    (p.take i).last = p i := by simp [take, last, Fin.last]

/-- Given the series `a₀ -r→ … -r→ aᵢ -r→ … -r→ aₙ`, the series `aᵢ₊₁ -r→ … -r→ aₙ`. -/
@[simps! length]
/-
**RelSeries.drop** 是 Mathlib 中的一个定义，位于命名空间 `RelSeries`。
形式化陈述：drop (p : RelSeries r) (i : Fin (p.length + 1)) : RelSeries r where length
参数：p : RelSeries r；i : Fin (p.length + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the series `a₀ -r→ … -r→ aᵢ -r→ … -r→ aₙ`, the series `aᵢ₊₁ -r→ … -r→ aₙ`.
-/
def drop (p : RelSeries r) (i : Fin (p.length + 1)) : RelSeries r where
  length := p.length - i
  toFun := fun ⟨j, h⟩ => p.toFun ⟨j+i, by lia⟩
  step := fun ⟨j, h⟩ => by
    convert! p.step ⟨j + i.1, by lia⟩
    simp only [Fin.succ_mk]; lia

@[simp]
/-
**RelSeries.head_drop** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：head_drop (p : RelSeries r) (i : Fin (p.length + 1)) : (p.drop i).head = p
.toFun i
参数：p : RelSeries r；i : Fin (p.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma head_drop (p : RelSeries r) (i : Fin (p.length + 1)) : (p.drop i).head = p.toFun i := by
  simp [drop, head]

@[simp]
/-
**RelSeries.last_drop** 是 Mathlib 中的一个引理，位于命名空间 `RelSeries`。
形式化陈述：last_drop (p : RelSeries r) (i : Fin (p.length + 1)) : (p.drop i).last = p
.last
参数：p : RelSeries r；i : Fin (p.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
lemma last_drop (p : RelSeries r) (i : Fin (p.length + 1)) : (p.drop i).last = p.last := by
  simp only [last, drop, Fin.last]
  congr
  lia

end RelSeries

variable {r} in
/-
**SetRel.not_finiteDimensional_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SetRel.not_finiteDimensional_iff [Nonempty α] : ¬ r.FiniteDimensional ↔ r.
InfiniteDimensional
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetRel.finiteDimensional_iff`：∀ {α : Type u_1} (r : SetRel α α), r.Finit
eDimensional ↔ ∃ x, ∀ (y : RelSeries r), y.length ≤ x.length
· 使用定理 `SetRel.infiniteDimensional_iff`：∀ {α : Type u_1} (r : SetRel α α), r.Inf
initeDimensional ↔ ∀ (n : ℕ), ∃ x, x.length = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma SetRel.not_finiteDimensional_iff [Nonempty α] :
    ¬ r.FiniteDimensional ↔ r.InfiniteDimensional := by
  rw [finiteDimensional_iff, infiniteDimensional_iff]
  push Not
  constructor
  · intro H n
    induction n with
    | zero => refine ⟨⟨0, ![_root_.Nonempty.some ‹_›], by simp⟩, by simp⟩
    | succ n IH =>
      obtain ⟨l, hl⟩ := IH
      obtain ⟨l', hl'⟩ := H l
      exact ⟨l'.take ⟨n + 1, by simpa [hl] using hl'⟩, rfl⟩
  · intro H l
    obtain ⟨l', hl'⟩ := H (l.length + 1)
    exact ⟨l', by simp [hl']⟩

variable {r} in
/-
**SetRel.not_infiniteDimensional_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SetRel.not_infiniteDimensional_iff [Nonempty α] : ¬ r.InfiniteDimensional 
↔ r.FiniteDimensional
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SetRel.not_finiteDimensional_iff`：SetRel.not_finiteDimensional_iff [None
mpty α] : ¬ r.FiniteDimensional ↔ r.InfiniteDimensional
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma SetRel.not_infiniteDimensional_iff [Nonempty α] :
    ¬ r.InfiniteDimensional ↔ r.FiniteDimensional := by
  rw [← not_finiteDimensional_iff, not_not]
/-
**SetRel.finiteDimensional_or_infiniteDimensional** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SetRel.finiteDimensional_or_infiniteDimensional [Nonempty α] : r.FiniteDim
ensional ∨ r.InfiniteDimensional
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SetRel.not_finiteDimensional_iff`：SetRel.not_finiteDimensional_iff [None
mpty α] : ¬ r.FiniteDimensional ↔ r.InfiniteDimensional
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
lemma SetRel.finiteDimensional_or_infiniteDimensional [Nonempty α] :
    r.FiniteDimensional ∨ r.InfiniteDimensional := by
  rw [← not_finiteDimensional_iff]
  exact em r.FiniteDimensional
/-
**SetRel.FiniteDimensional.inv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SetRel.FiniteDimensional.inv [FiniteDimensional r] : FiniteDimensional r.i
nv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.length_le_length_longestOf`：length_le_length_longestOf [r.Fini
teDimensional] (x : RelSeries r) : x.length <= (RelSeries.longestOf r).length
-/
instance SetRel.FiniteDimensional.inv [FiniteDimensional r] : FiniteDimensional r.inv :=
  ⟨.reverse (.longestOf r), fun s ↦ s.reverse.length_le_length_longestOf r⟩

variable {r} in
@[simp]
/-
**SetRel.finiteDimensional_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SetRel.finiteDimensional_inv : FiniteDimensional r.inv ↔ FiniteDimensional
 r
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma SetRel.finiteDimensional_inv : FiniteDimensional r.inv ↔ FiniteDimensional r :=
  ⟨fun _ ↦ .inv r.inv, fun _ ↦ .inv _⟩
/-
**SetRel.InfiniteDimensional.inv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SetRel.InfiniteDimensional.inv [InfiniteDimensional r] : InfiniteDimension
al r.inv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RelSeries.length_withLength`：∀ {α : Type u_1} (r : SetRel α α) [inst : r
.InfiniteDimensional] (n : ℕ), (RelSeries.withLength r n).length = n
-/
instance SetRel.InfiniteDimensional.inv [InfiniteDimensional r] : InfiniteDimensional r.inv :=
  ⟨fun n ↦ ⟨.reverse (.withLength r n), RelSeries.length_withLength r n⟩⟩

variable {r} in
@[simp]
/-
**SetRel.infiniteDimensional_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SetRel.infiniteDimensional_inv : InfiniteDimensional r.inv ↔ InfiniteDimen
sional r
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma SetRel.infiniteDimensional_inv : InfiniteDimensional r.inv ↔ InfiniteDimensional r :=
  ⟨fun _ ↦ .inv r.inv, fun _ ↦ .inv _⟩
/-
**SetRel.IsWellFounded.inv_of_finiteDimensional** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SetRel.IsWellFounded.inv_of_finiteDimensional [r.FiniteDimensional] : r.in
v.IsWellFounded
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetRel.IsWellFounded.eq_1`：∀ {α : Type u_1} (R : SetRel α α), R.IsWellFo
unded = WellFounded fun x1 x2 => (x1, x2) ∈ R
· 使用定理 `wellFounded_iff_isEmpty_descending_chain`：wellFounded_iff_isEmpty_descen
ding_chain {α} {r : α -> α -> Prop} : WellFounded r ↔ IsEmpty { f : Nat -> α // 
forall n, r (f (n + 1)) (f n) …
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用引理 `RelSeries.length_le_length_longestOf`：length_le_length_longestOf [r.Fini
teDimensional] (x : RelSeries r) : x.length <= (RelSeries.longestOf r).length
-/
lemma SetRel.IsWellFounded.inv_of_finiteDimensional [r.FiniteDimensional] :
    r.inv.IsWellFounded := by
  rw [IsWellFounded, wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_⟩
  let s := RelSeries.mk (r := r) ((RelSeries.longestOf r).length + 1) (f ·) (hf ·)
  exact (RelSeries.longestOf r).length.lt_succ_self.not_ge s.length_le_length_longestOf
/-
**SetRel.IsWellFounded.of_finiteDimensional** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SetRel.IsWellFounded.of_finiteDimensional [r.FiniteDimensional] : r.IsWell
Founded
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.IsWellFounded.inv_of_finiteDimensional`：SetRel.IsWellFounded.inv_
of_finiteDimensional [r.FiniteDimensional] : r.inv.IsWellFounded
-/
lemma SetRel.IsWellFounded.of_finiteDimensional [r.FiniteDimensional] : r.IsWellFounded :=
  .inv_of_finiteDimensional r.inv

/-- A type is finite dimensional if its `LTSeries` has bounded length. -/
/-
**FiniteDimensionalOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：FiniteDimensionalOrder (γ : Type*) [Preorder γ]
参数：γ : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type is finite dimensional if its `LTSeries` has bounded length.
-/
abbrev FiniteDimensionalOrder (γ : Type*) [Preorder γ] :=
  SetRel.FiniteDimensional {(a, b) : γ × γ | a < b}
/-
**FiniteDimensionalOrder.ofUnique** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：FiniteDimensionalOrder.ofUnique (γ : Type*) [Preorder γ] [Unique γ] : Fini
teDimensionalOrder γ where exists_longest_relSeries
参数：γ : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
instance FiniteDimensionalOrder.ofUnique (γ : Type*) [Preorder γ] [Unique γ] :
    FiniteDimensionalOrder γ where
  exists_longest_relSeries := ⟨.singleton _ default, fun x ↦ by
    by_contra! r
    exact (x.step ⟨0, by lia⟩).ne <| Subsingleton.elim _ _⟩

/-- A type is infinite dimensional if it has `LTSeries` of at least arbitrary length -/
/-
**InfiniteDimensionalOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：InfiniteDimensionalOrder (γ : Type*) [Preorder γ]
参数：γ : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type is infinite dimensional if it has `LTSeries` of at least arbitrary length
-/
abbrev InfiniteDimensionalOrder (γ : Type*) [Preorder γ] :=
  SetRel.InfiniteDimensional {(a, b) : γ × γ | a < b}

section LTSeries

variable (α) [Preorder α] [Preorder β]
/--
If `α` is a preorder, a LTSeries is a relation series of the less than relation.
-/
/-
**LTSeries** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LTSeries
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is a preorder, a LTSeries is a relation series of the less than relation.
-/
abbrev LTSeries := RelSeries {(a, b) : α × α | a < b}

namespace LTSeries

/-- The longest `<`-series when a type is finite dimensional -/
/-
**LTSeries.longestOf** 是 Mathlib 中的一个定义，位于命名空间 `LTSeries`。
形式化陈述：(α : Type u_1) → [inst : Preorder α] → [FiniteDimensionalOrder α] → LTSeri
es α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The longest `<`-series when a type is finite dimensional
-/
protected noncomputable def longestOf [FiniteDimensionalOrder α] : LTSeries α :=
  RelSeries.longestOf _

/-- A `<`-series with length `n` if the relation is infinite dimensional -/
/-
**LTSeries.withLength** 是 Mathlib 中的一个定义，位于命名空间 `LTSeries`。
形式化陈述：(α : Type u_1) → [inst : Preorder α] → [InfiniteDimensionalOrder α] → ℕ → 
LTSeries α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `<`-series with length `n` if the relation is infinite dimensional
-/
protected noncomputable def withLength [InfiniteDimensionalOrder α] (n : ℕ) : LTSeries α :=
  RelSeries.withLength _ n
/-
**LTSeries.length_withLength** 是 Mathlib 中的一个定理，位于命名空间 `LTSeries`。
形式化陈述：∀ (α : Type u_1) [inst : Preorder α] [inst_1 : InfiniteDimensionalOrder α]
 (n : ℕ), (LTSeries.withLength α n).length = n
参数：α : Type u_1；n : ℕ；LTSeries.withLength α n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelSeries.length_withLength`：∀ {α : Type u_1} (r : SetRel α α) [inst : r
.InfiniteDimensional] (n : ℕ), (RelSeries.withLength r n).length = n
-/
@[simp] lemma length_withLength [InfiniteDimensionalOrder α] (n : ℕ) :
    (LTSeries.withLength α n).length = n :=
  RelSeries.length_withLength _ _

/-- if `α` is infinite dimensional, then `α` is nonempty. -/
/-
**LTSeries.nonempty_of_infiniteDimensionalOrder** 是 Mathlib 中的一个引理，位于命名空间 `LTSer
ies`。
形式化陈述：nonempty_of_infiniteDimensionalOrder [InfiniteDimensionalOrder α] : Nonemp
ty α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
if `α` is infinite dimensional, then `α` is nonempty.
-/
lemma nonempty_of_infiniteDimensionalOrder [InfiniteDimensionalOrder α] : Nonempty α :=
  ⟨LTSeries.withLength α 0 0⟩
/-
**LTSeries.nonempty_of_finiteDimensionalOrder** 是 Mathlib 中的一个引理，位于命名空间 `LTSerie
s`。
形式化陈述：nonempty_of_finiteDimensionalOrder [FiniteDimensionalOrder α] : Nonempty α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetRel.finiteDimensional_iff`：∀ {α : Type u_1} (r : SetRel α α), r.Finit
eDimensional ↔ ∃ x, ∀ (y : RelSeries r), y.length ≤ x.length
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma nonempty_of_finiteDimensionalOrder [FiniteDimensionalOrder α] : Nonempty α := by
  obtain ⟨p, _⟩ := (SetRel.finiteDimensional_iff _).mp ‹_›
  exact ⟨p 0⟩

variable {α}
/-
**LTSeries.longestOf_is_longest** 是 Mathlib 中的一个引理，位于命名空间 `LTSeries`。
形式化陈述：longestOf_is_longest [FiniteDimensionalOrder α] (x : LTSeries α) : x.lengt
h <= (LTSeries.longestOf α).length
参数：x : LTSeries α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.length_le_length_longestOf`：length_le_length_longestOf [r.Fini
teDimensional] (x : RelSeries r) : x.length <= (RelSeries.longestOf r).length
-/
lemma longestOf_is_longest [FiniteDimensionalOrder α] (x : LTSeries α) :
    x.length ≤ (LTSeries.longestOf α).length :=
  RelSeries.length_le_length_longestOf _ _
/-
**LTSeries.longestOf_len_unique** 是 Mathlib 中的一个引理，位于命名空间 `LTSeries`。
形式化陈述：longestOf_len_unique [FiniteDimensionalOrder α] (p : LTSeries α) (is_longe
st : forall (q : LTSeries α), q.length <= p.length) : p.length = (LTSeries.longe
stOf α).length
参数：p : LTSeries α；is_longest : forall (q : LTSeries α), q.length <= p.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `LTSeries.longestOf_is_longest`：longestOf_is_longest [FiniteDimensionalOr
der α] (x : LTSeries α) : x.length <= (LTSeries.longestOf α).length
-/
lemma longestOf_len_unique [FiniteDimensionalOrder α] (p : LTSeries α)
    (is_longest : ∀ (q : LTSeries α), q.length ≤ p.length) :
    p.length = (LTSeries.longestOf α).length :=
  le_antisymm (longestOf_is_longest _) (is_longest _)
/-
**LTSeries.strictMono** 是 Mathlib 中的一个引理，位于命名空间 `LTSeries`。
形式化陈述：strictMono (x : LTSeries α) : StrictMono x
参数：x : LTSeries α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RelSeries.rel_of_lt`：rel_of_lt [r.IsTrans] (x : RelSeries r) {i j : Fin 
(x.length + 1)} (h : i < j) : x i ~[r] x j
· 使用定理 `SetRel.instIsTransOfPredProdMatch_1PropOfIsTrans`：∀ {α : Type u_1} {R : 
α → α → Prop} [IsTrans α R], SetRel.IsTrans {(a, b) | R a b}
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
lemma strictMono (x : LTSeries α) : StrictMono x :=
  fun _ _ h => x.rel_of_lt h
/-
**LTSeries.monotone** 是 Mathlib 中的一个引理，位于命名空间 `LTSeries`。
形式化陈述：monotone (x : LTSeries α) : Monotone x
参数：x : LTSeries α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `LTSeries.strictMono`：strictMono (x : LTSeries α) : StrictMono x
-/
lemma monotone (x : LTSeries α) : Monotone x :=
  x.strictMono.monotone
/-
**LTSeries.head_le** 是 Mathlib 中的一个引理，位于命名空间 `LTSeries`。
形式化陈述：head_le (x : LTSeries α) (n : Fin (x.length + 1)) : x.head <= x n
参数：x : LTSeries α；n : Fin (x.length + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LTSeries.monotone`：monotone (x : LTSeries α) : Monotone x
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma head_le (x : LTSeries α) (n : Fin (x.length + 1)) : x.head ≤ x n :=
  x.monotone (Fin.zero_le n)
/-
**LTSeries.head_le_last** 是 Mathlib 中的一个引理，位于命名空间 `LTSeries`。
形式化陈述：head_le_last (x : LTSeries α) : x.head <= x.last
参数：x : LTSeries α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LTSeries.head_le`：head_le (x : LTSeries α) (n : Fin (x.length + 1)) : x.
head <= x n
-/
lemma head_le_last (x : LTSeries α) : x.head ≤ x.last := x.head_le _

/-- An alternative constructor of `LTSeries` from a strictly monotone function. -/
@[simps]
/-
**LTSeries.mk** 是 Mathlib 中的一个定义，位于命名空间 `LTSeries`。
形式化陈述：mk (length : Nat) (toFun : Fin (length + 1) -> α) (strictMono : StrictMono
 toFun) : LTSeries α where length
参数：length : Nat；toFun : Fin (length + 1) -> α；strictMono : StrictMono toFun。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative constructor of `LTSeries` from a strictly monotone function.
-/
def mk (length : ℕ) (toFun : Fin (length + 1) → α) (strictMono : StrictMono toFun) :
    LTSeries α where
  length := length
  toFun := toFun
  step i := strictMono <| lt_add_one i.1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An injection from the type of strictly monotone functions with limited length to `LTSeries`. -/
/-
**LTSeries.injStrictMono** 是 Mathlib 中的一个定义，位于命名空间 `LTSeries`。
形式化陈述：injStrictMono (n : Nat) : {f : (l : Fin n) × (Fin (l + 1) -> α) // StrictM
ono f.2} ↪ LTSeries α where toFun f
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injection from the type of strictly monotone functions with limited length to
 `LTSeries`.
-/
def injStrictMono (n : ℕ) :
    {f : (l : Fin n) × (Fin (l + 1) → α) // StrictMono f.2} ↪ LTSeries α where
  toFun f := mk f.1.1 f.1.2 f.2
  inj' f g e := by
    obtain ⟨⟨lf, f⟩, mf⟩ := f
    obtain ⟨⟨lg, g⟩, mg⟩ := g
    dsimp only at mf mg e
    have leq := congr($(e).length)
    rw [mk_length lf f mf, mk_length lg g mg, Fin.val_eq_val] at leq
    subst leq
    simp_rw [Subtype.mk_eq_mk, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    have feq := fun i ↦ congr($(e).toFun i)
    simp_rw [mk_toFun lf f mf, mk_toFun lf g mg, mk_length lf f mf] at feq
    rwa [funext_iff]

/--
For two preorders `α, β`, if `f : α → β` is strictly monotonic, then a strict chain of `α`
can be pushed out to a strict chain of `β` by
`a₀ < a₁ < ... < aₙ ↦ f a₀ < f a₁ < ... < f aₙ`
-/
@[simps!]
/-
**LTSeries.map** 是 Mathlib 中的一个定义，位于命名空间 `LTSeries`。
形式化陈述：map (p : LTSeries α) (f : α -> β) (hf : StrictMono f) : LTSeries β
参数：p : LTSeries α；f : α -> β；hf : StrictMono f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For two preorders `α, β`, if `f : α → β` is strictly monotonic, then a strict ch
ain of `α`
can be pushed out to a strict chain of `β` by
`a₀ < a₁ < ... < aₙ ↦ f a₀ < f a₁ < ... < f aₙ`
-/
def map (p : LTSeries α) (f : α → β) (hf : StrictMono f) : LTSeries β :=
  LTSeries.mk p.length (f.comp p) (hf.comp p.strictMono)
/-
**LTSeries.head_map** 是 Mathlib 中的一个定理，位于命名空间 `LTSeries`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
(p : LTSeries α) (f : α → β)   (hf : StrictMono f), RelSeries.head (p.map f hf) 
= f (RelSeries.head p)
参数：p : LTSeries α；f : α → β；hf : StrictMono f；p.map f hf；RelSeries.head p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma head_map (p : LTSeries α) (f : α → β) (hf : StrictMono f) :
    (p.map f hf).head = f p.head := rfl
/-
**LTSeries.last_map** 是 Mathlib 中的一个定理，位于命名空间 `LTSeries`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
(p : LTSeries α) (f : α → β)   (hf : StrictMono f), RelSeries.last (p.map f hf) 
= f (RelSeries.last p)
参数：p : LTSeries α；f : α → β；hf : StrictMono f；p.map f hf；RelSeries.last p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma last_map (p : LTSeries α) (f : α → β) (hf : StrictMono f) :
    (p.map f hf).last = f p.last := rfl

/--
For two preorders `α, β`, if `f : α → β` is surjective and strictly comonotonic, then a
strict series of `β` can be pulled back to a strict chain of `α` by
`b₀ < b₁ < ... < bₙ ↦ f⁻¹ b₀ < f⁻¹ b₁ < ... < f⁻¹ bₙ` where `f⁻¹ bᵢ` is an arbitrary element in the
preimage of `f⁻¹ {bᵢ}`.
-/
@[simps!]
/-
**LTSeries.comap** 是 Mathlib 中的一个定义，位于命名空间 `LTSeries`。
形式化陈述：comap (p : LTSeries β) (f : α -> β) (comap : forall ⦃x y⦄, f x < f y -> x 
< y) (surjective : Function.Surjective f) : LTSeries α
参数：p : LTSeries β；f : α -> β；comap : forall ⦃x y⦄, f x < f y -> x < y；surjective
 : Function.Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For two preorders `α, β`, if `f : α → β` is surjective and strictly comonotonic,
 then a
strict series of `β` can be pulled back to a strict chain of `α` by
`b₀ < b₁ < ... < bₙ ↦ f⁻¹ b₀ < f⁻¹ b₁ < ... < f⁻¹ bₙ` where `f⁻¹ bᵢ` is an arbit
rary element in the
preimage of `f⁻¹ {bᵢ}`.
-/
noncomputable def comap (p : LTSeries β) (f : α → β)
    (comap : ∀ ⦃x y⦄, f x < f y → x < y)
    (surjective : Function.Surjective f) :
    LTSeries α :=
  mk p.length (fun i ↦ (surjective (p i)).choose)
    (fun i j h ↦ comap (by simpa only [(surjective _).choose_spec] using p.strictMono h))

/-- The strict series `0 < … < n` in `ℕ`. -/
/-
**LTSeries.range** 是 Mathlib 中的一个定义，位于命名空间 `LTSeries`。
形式化陈述：range (n : Nat) : LTSeries Nat where length
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The strict series `0 < … < n` in `ℕ`.
-/
def range (n : ℕ) : LTSeries ℕ where
  length := n
  toFun := fun i => i
  step i := Nat.lt_add_one i
/-
**LTSeries.length_range** 是 Mathlib 中的一个定理，位于命名空间 `LTSeries`。
形式化陈述：∀ (n : ℕ), (LTSeries.range n).length = n
参数：n : ℕ；LTSeries.range n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma length_range (n : ℕ) : (range n).length = n := rfl
/-
**LTSeries.range_apply** 是 Mathlib 中的一个定理，位于命名空间 `LTSeries`。
形式化陈述：∀ (n : ℕ) (i : Fin (n + 1)), (LTSeries.range n).toFun i = ↑i
参数：n : ℕ；i : Fin (n + 1)；LTSeries.range n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma range_apply (n : ℕ) (i : Fin (n + 1)) : (range n) i = i := rfl
/-
**LTSeries.head_range** 是 Mathlib 中的一个定理，位于命名空间 `LTSeries`。
形式化陈述：∀ (n : ℕ), RelSeries.head (LTSeries.range n) = 0
参数：n : ℕ；LTSeries.range n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma head_range (n : ℕ) : (range n).head = 0 := rfl
/-
**LTSeries.last_range** 是 Mathlib 中的一个定理，位于命名空间 `LTSeries`。
形式化陈述：∀ (n : ℕ), RelSeries.last (LTSeries.range n) = n
参数：n : ℕ；LTSeries.range n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma last_range (n : ℕ) : (range n).last = n := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Any `LTSeries` can be refined to a `CovBy`-`RelSeries`
in a bidirectionally well-founded order. -/
/-
**LTSeries.exists_relSeries_covBy** 是 Mathlib 中的一个定理，位于命名空间 `LTSeries`。
形式化陈述：exists_relSeries_covBy {α} [PartialOrder α] [WellFoundedLT α] [WellFounded
GT α] (s : LTSeries α) : exists (t : RelSeries {(a, b) : α × α | a ⋖ b}) (i : Fi
n (s.length + 1) ↪ Fin (t.length + 1)), t ∘ i = s ∧ i 0 = 0 ∧ i (.last _) = .las
t _
参数：s : LTSeries α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le`：exists_covBy_seq_
of_wellFoundedLT_wellFoundedGT_of_le {α : Type*} [PartialOrder α] [wfl : WellFou
ndedLT α] [wfg : WellFoundedGT α] {x y : α}…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RelSeries.smash_length`：∀ {α : Type u_1} {r : SetRel α α} (p q : RelSeri
es r) (connect : p.last = q.head),   (p.smash q connect).length = p.length + q.l
ength
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
Any `LTSeries` can be refined to a `CovBy`-`RelSeries`
in a bidirectionally well-founded order.
-/
theorem exists_relSeries_covBy
    {α} [PartialOrder α] [WellFoundedLT α] [WellFoundedGT α] (s : LTSeries α) :
    ∃ (t : RelSeries {(a, b) : α × α | a ⋖ b}) (i : Fin (s.length + 1) ↪ Fin (t.length + 1)),
      t ∘ i = s ∧ i 0 = 0 ∧ i (.last _) = .last _ := by
  obtain ⟨n, s, h⟩ := s
  induction n with
  | zero => exact ⟨⟨0, s, nofun⟩, (Equiv.refl _).toEmbedding, rfl, rfl, rfl⟩
  | succ n IH =>
    obtain ⟨t₁, i, ht, hi₁, hi₂⟩ := IH (s ∘ Fin.castSucc) fun _ ↦ h _
    obtain ⟨t₂, h₁, m, h₂, ht₂⟩ :=
      exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le (h (.last _)).le
    let t₃ : RelSeries {(a, b) : α × α | a ⋖ b} := ⟨m, (t₂ ·), fun i ↦ by simpa using! ht₂ i⟩
    have H : t₁.last = t₂ 0 := (congr(t₁ $hi₂.symm).trans (congr_fun ht _)).trans h₁.symm
    refine ⟨t₁.smash t₃ H, ⟨Fin.snoc (Fin.castLE (by simp) ∘ i) (.last _), ?_⟩, ?_, ?_, ?_⟩
    · refine Fin.lastCases (Fin.lastCases (fun _ ↦ rfl) fun j eq ↦ ?_) fun j ↦ Fin.lastCases
        (fun eq ↦ ?_) fun k eq ↦ Fin.ext (congr_arg Fin.val (by simpa using! eq) :)
      on_goal 2 => rw [eq_comm] at eq
      all_goals
        rw [Fin.snoc_castSucc] at eq
        obtain rfl : m = 0 := by simpa [t₃] using! (congr_arg Fin.val eq).trans_lt (i j).2
        cases (h (.last _)).ne' (h₂.symm.trans h₁)
    · refine funext (Fin.lastCases ?_ fun j ↦ ?_)
      · convert! h₂; simpa using! RelSeries.last_smash ..
      convert! congr_fun ht j using 1
      simp [RelSeries.smash_castLE]
    all_goals simp [Fin.snoc, Fin.castPred_zero, hi₁]

set_option backward.isDefEq.respectTransparency false in
/-
**LTSeries.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot** 是 Mathlib 中的
一个定理，位于命名空间 `LTSeries`。
形式化陈述：exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot {α} [PartialOrder α
] [BoundedOrder α] [WellFoundedLT α] [WellFoundedGT α] (s : LTSeries α) : exists
 (t : RelSeries {(a, b) : α × α | a ⋖ b}) (i : Fin (s.length + 1) ↪ Fin (t.lengt
h + 1)), t ∘ i = s ∧ t.head = ⊥ ∧ t.last = ⊤
参数：s : LTSeries α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LTSeries.exists_relSeries_covBy`：exists_relSeries_covBy {α} [PartialOrde
r α] [WellFoundedLT α] [WellFoundedGT α] (s : LTSeries α) : exists (t : RelSerie
s {(a, b) : α × α | a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RelSeries.head.eq_1`：∀ {α : Type u_1} {r : SetRel α α} (x : RelSeries r)
, x.head = x.toFun 0
· 使用定理 `Function.comp.eq_1`：∀ {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ)
 (g : α → β) (x : α), (f ∘ g) x = f (g x)
· 使用定理 `RelSeries.last.eq_1`：∀ {α : Type u_1} {r : SetRel α α} (x : RelSeries r)
, x.last = x.toFun (Fin.last x.length)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RelSeries.head_snoc`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r)
 (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).head = p.he
ad
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RelSeries.last_snoc`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r)
 (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).last = newL
ast
· 使用定理 `RelSeries.snoc_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries 
r) (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).length = 
p.length + …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用引理 `RelSeries.snoc_cast_castSucc`：snoc_cast_castSucc (s : RelSeries r) (a : 
α) (h : s.last ~[r] a) (i : Fin (s.length + 1)) : (s.snoc a h) (.cast (by simp) 
(.castSucc i)) = s…
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `RelSeries.cons_length`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries 
r) (newHead : α) (rel : (newHead, p.head) ∈ r),   (p.cons newHead rel).length = 
p.length + …
· 使用定理 `Nat.succ.inj`：∀ {m n : ℕ}, m.succ = n.succ → m = n
· 使用引理 `RelSeries.cons_cast_succ`：cons_cast_succ (s : RelSeries r) (a : α) (h : 
a ~[r] s.head) (i : Fin (s.length + 1)) : (s.cons a h) (.cast (by simp) (.succ i
)) = s i
-/
theorem exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
    {α} [PartialOrder α] [BoundedOrder α] [WellFoundedLT α] [WellFoundedGT α] (s : LTSeries α) :
    ∃ (t : RelSeries {(a, b) : α × α | a ⋖ b}) (i : Fin (s.length + 1) ↪ Fin (t.length + 1)),
      t ∘ i = s ∧ t.head = ⊥ ∧ t.last = ⊤ := by
  wlog h₁ : s.head = ⊥
  · obtain ⟨t, i, hi, ht⟩ := this (s.cons ⊥ (bot_lt_iff_ne_bot.mpr h₁)) rfl
    exact ⟨t, ⟨fun j ↦ i (j.succ.cast (by simp)), fun _ _ ↦ by simp⟩,
      funext fun j ↦ (congr_fun hi _).trans (RelSeries.cons_cast_succ _ _ _ _), ht⟩
  wlog h₂ : s.last = ⊤
  · obtain ⟨t, i, hi, ht⟩ := this (s.snoc ⊤ (lt_top_iff_ne_top.mpr h₂)) (by simp [h₁]) (by simp)
    exact ⟨t, ⟨fun j ↦ i (.cast (by simp) j.castSucc), fun _ _ ↦ by simp⟩,
      funext fun j ↦ (congr_fun hi _).trans (RelSeries.snoc_cast_castSucc _ _ _ _), ht⟩
  obtain ⟨t, i, hit, hi₁, hi₂⟩ := s.exists_relSeries_covBy
  refine ⟨t, i, hit, ?_, ?_⟩
  · rw [← h₁, RelSeries.head, RelSeries.head, ← hi₁, ← hit, Function.comp]
  · rw [← h₂, RelSeries.last, RelSeries.last, ← hi₂, ← hit, Function.comp]

/--
In ℕ, two entries in an `LTSeries` differ by at least the difference of their indices.
(Expressed in a way that avoids subtraction).
-/
/-
**LTSeries.apply_add_index_le_apply_add_index_nat** 是 Mathlib 中的一个引理，位于命名空间 `LTS
eries`。
形式化陈述：apply_add_index_le_apply_add_index_nat (p : LTSeries Nat) (i j : Fin (p.le
ngth + 1)) (hij : i <= j) : p i + j <= p j + i
参数：p : LTSeries Nat；i j : Fin (p.length + 1)；hij : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
· 使用定理 `Nat.lt_of_succ_lt`：∀ {n m : ℕ}, n.succ < m → n < m

--- 原说明 ---
In ℕ, two entries in an `LTSeries` differ by at least the difference of their in
dices.
(Expressed in a way that avoids subtraction).
-/
lemma apply_add_index_le_apply_add_index_nat (p : LTSeries ℕ) (i j : Fin (p.length + 1))
    (hij : i ≤ j) : p i + j ≤ p j + i := by
  have ⟨i, hi⟩ := i
  have ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  simp only at *
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _hij ih =>
    specialize ih (Nat.lt_of_succ_lt hj)
    have step : p ⟨j, _⟩ < p ⟨j + 1, _⟩ := p.step ⟨j, by lia⟩
    lia

/--
In ℤ, two entries in an `LTSeries` differ by at least the difference of their indices.
(Expressed in a way that avoids subtraction).
-/
/-
**LTSeries.apply_add_index_le_apply_add_index_int** 是 Mathlib 中的一个引理，位于命名空间 `LTS
eries`。
形式化陈述：apply_add_index_le_apply_add_index_int (p : LTSeries Int) (i j : Fin (p.le
ngth + 1)) (hij : i <= j) : p i + j <= p j + i
参数：p : LTSeries Int；i j : Fin (p.length + 1)；hij : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
· 使用定理 `Nat.lt_of_succ_lt`：∀ {n m : ℕ}, n.succ < m → n < m

--- 原说明 ---
In ℤ, two entries in an `LTSeries` differ by at least the difference of their in
dices.
(Expressed in a way that avoids subtraction).
-/
lemma apply_add_index_le_apply_add_index_int (p : LTSeries ℤ) (i j : Fin (p.length + 1))
    (hij : i ≤ j) : p i + j ≤ p j + i := by
  -- The proof is identical to `LTSeries.apply_add_index_le_apply_add_index_nat`, but seemed easier
  -- to copy rather than to abstract
  have ⟨i, hi⟩ := i
  have ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  simp only at *
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _hij ih =>
    specialize ih (Nat.lt_of_succ_lt hj)
    have step : p ⟨j, _⟩ < p ⟨j + 1, _⟩ := p.step ⟨j, by lia⟩
    lia

/-- In ℕ, the head and tail of an `LTSeries` differ at least by the length of the series -/
/-
**LTSeries.head_add_length_le_nat** 是 Mathlib 中的一个引理，位于命名空间 `LTSeries`。
形式化陈述：head_add_length_le_nat (p : LTSeries Nat) : p.head + p.length <= p.last
参数：p : LTSeries Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LTSeries.apply_add_index_le_apply_add_index_nat`：apply_add_index_le_appl
y_add_index_nat (p : LTSeries Nat) (i j : Fin (p.length + 1)) (hij : i <= j) : p
 i + j <= p j + i
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a

--- 原说明 ---
In ℕ, the head and tail of an `LTSeries` differ at least by the length of the se
ries
-/
lemma head_add_length_le_nat (p : LTSeries ℕ) : p.head + p.length ≤ p.last :=
  LTSeries.apply_add_index_le_apply_add_index_nat _ _ (Fin.last _) (Fin.zero_le _)

/-- In ℤ, the head and tail of an `LTSeries` differ at least by the length of the series -/
/-
**LTSeries.head_add_length_le_int** 是 Mathlib 中的一个引理，位于命名空间 `LTSeries`。
形式化陈述：head_add_length_le_int (p : LTSeries Int) : p.head + p.length <= p.last
参数：p : LTSeries Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `LTSeries.apply_add_index_le_apply_add_index_int`：apply_add_index_le_appl
y_add_index_int (p : LTSeries Int) (i j : Fin (p.length + 1)) (hij : i <= j) : p
 i + j <= p j + i
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a

--- 原说明 ---
In ℤ, the head and tail of an `LTSeries` differ at least by the length of the se
ries
-/
lemma head_add_length_le_int (p : LTSeries ℤ) : p.head + p.length ≤ p.last := by
  simpa using! LTSeries.apply_add_index_le_apply_add_index_int _ _ (Fin.last _) (Fin.zero_le _)

section Fintype

variable [Fintype α]

/-
**LTSeries.length_lt_card** 是 Mathlib 中的一个引理，位于命名空间 `LTSeries`。
形式化陈述：length_lt_card (s : LTSeries α) : s.length < Fintype.card α
参数：s : LTSeries α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Fintype.exists_ne_map_eq_of_card_lt`：exists_ne_map_eq_of_card_lt (f : α 
-> β) (h : Fintype.card β < Fintype.card α) : exists x y, x != y ∧ f x = f y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `LTSeries.strictMono`：strictMono (x : LTSeries α) : StrictMono x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma length_lt_card (s : LTSeries α) : s.length < Fintype.card α := by
  by_contra! h
  obtain ⟨i, j, hn, he⟩ := Fintype.exists_ne_map_eq_of_card_lt s (by rw [Fintype.card_fin]; lia)
  wlog hl : i < j generalizing i j
  · exact this j i hn.symm he.symm (by lia)
  exact absurd he (s.strictMono hl).ne
/-
**LTSeries.** 是 Mathlib 中的一个实例，位于命名空间 `LTSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableLT α] : Fintype (LTSeries α) where
  elems := Finset.univ.map (injStrictMono (Fintype.card α))
  complete s := by
    have bl := s.length_lt_card
    obtain ⟨l, f, mf⟩ := s
    simp_rw [Finset.mem_map, Finset.mem_univ, true_and, Subtype.exists]
    use ⟨⟨l, bl⟩, f⟩, Fin.strictMono_iff_lt_succ.mpr mf; rfl

end Fintype

end LTSeries

end LTSeries

/-
**not_finiteDimensionalOrder_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_finiteDimensionalOrder_iff [Preorder α] [Nonempty α] : ¬ FiniteDimensi
onalOrder α ↔ InfiniteDimensionalOrder α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.not_finiteDimensional_iff`：SetRel.not_finiteDimensional_iff [None
mpty α] : ¬ r.FiniteDimensional ↔ r.InfiniteDimensional
-/
lemma not_finiteDimensionalOrder_iff [Preorder α] [Nonempty α] :
    ¬ FiniteDimensionalOrder α ↔ InfiniteDimensionalOrder α :=
  SetRel.not_finiteDimensional_iff
/-
**not_infiniteDimensionalOrder_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_infiniteDimensionalOrder_iff [Preorder α] [Nonempty α] : ¬ InfiniteDim
ensionalOrder α ↔ FiniteDimensionalOrder α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.not_infiniteDimensional_iff`：SetRel.not_infiniteDimensional_iff [
Nonempty α] : ¬ r.InfiniteDimensional ↔ r.FiniteDimensional
-/
lemma not_infiniteDimensionalOrder_iff [Preorder α] [Nonempty α] :
    ¬ InfiniteDimensionalOrder α ↔ FiniteDimensionalOrder α :=
  SetRel.not_infiniteDimensional_iff

variable (α) in
/-
**finiteDimensionalOrder_or_infiniteDimensionalOrder** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：finiteDimensionalOrder_or_infiniteDimensionalOrder [Preorder α] [Nonempty 
α] : FiniteDimensionalOrder α ∨ InfiniteDimensionalOrder α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.finiteDimensional_or_infiniteDimensional`：SetRel.finiteDimensiona
l_or_infiniteDimensional [Nonempty α] : r.FiniteDimensional ∨ r.InfiniteDimensio
nal
-/
lemma finiteDimensionalOrder_or_infiniteDimensionalOrder [Preorder α] [Nonempty α] :
    FiniteDimensionalOrder α ∨ InfiniteDimensionalOrder α :=
  SetRel.finiteDimensional_or_infiniteDimensional _

/-- If `f : α → β` is a strictly monotonic function and `α` is an infinite-dimensional type then so
  is `β`. -/
/-
**infiniteDimensionalOrder_of_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：infiniteDimensionalOrder_of_strictMono [Preorder α] [Preorder β] (f : α ->
 β) (hf : StrictMono f) [InfiniteDimensionalOrder α] : InfiniteDimensionalOrder 
β
参数：f : α -> β；hf : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LTSeries.length_withLength`：∀ (α : Type u_1) [inst : Preorder α] [inst_1
 : InfiniteDimensionalOrder α] (n : ℕ), (LTSeries.withLength α n).length = n

--- 原说明 ---
If `f : α → β` is a strictly monotonic function and `α` is an infinite-dimension
al type then so
  is `β`.
-/
lemma infiniteDimensionalOrder_of_strictMono [Preorder α] [Preorder β]
    (f : α → β) (hf : StrictMono f) [InfiniteDimensionalOrder α] :
    InfiniteDimensionalOrder β :=
  ⟨fun n ↦ ⟨(LTSeries.withLength _ n).map f hf, LTSeries.length_withLength α n⟩⟩
