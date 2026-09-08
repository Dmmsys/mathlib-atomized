/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.List.Duplicate
public import Mathlib.Data.List.Sort

/-!
# Equivalence between `Fin (length l)` and elements of a list

Given a list `l`,

* if `l` has no duplicates, then `List.Nodup.getEquiv` is the equivalence between
  `Fin (length l)` and `{x // x ∈ l}` sending `i` to `⟨get l i, _⟩` with the inverse
  sending `⟨x, hx⟩` to `⟨indexOf x l, _⟩`;

* if `l` has no duplicates and contains every element of a type `α`, then
  `List.Nodup.getEquivOfForallMemList` defines an equivalence between `Fin (length l)` and `α`;
  if `α` does not have decidable equality, then
  there is a bijection `List.Nodup.getBijectionOfForallMemList`;

* if `l` is sorted w.r.t. `(<)`, then `List.SortedLT.getIso` is the same bijection reinterpreted
  as an `OrderIso`.

-/

@[expose] public section


namespace List

variable {α : Type*}

namespace Nodup

/-- If `l` lists all the elements of `α` without duplicates, then `List.get` defines
a bijection `Fin l.length → α`.  See `List.Nodup.getEquivOfForallMemList`
for a version giving an equivalence when there is decidable equality. -/
@[simps]
/-
**List.Nodup.getBijectionOfForallMemList** 是 Mathlib 中的一个定义，位于命名空间 `List.Nodup`。
形式化陈述：getBijectionOfForallMemList (l : List α) (nd : l.Nodup) (h : forall x : α,
 x in l) : { f : Fin l.length -> α // Function.Bijective f }
参数：l : List α；nd : l.Nodup；h : forall x : α, x in l。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `l` lists all the elements of `α` without duplicates, then `List.get` defines
a bijection `Fin l.length → α`.  See `List.Nodup.getEquivOfForallMemList`
for a version giving an equivalence when there is decidable equality.
-/
def getBijectionOfForallMemList (l : List α) (nd : l.Nodup) (h : ∀ x : α, x ∈ l) :
    { f : Fin l.length → α // Function.Bijective f } :=
  ⟨fun i => l.get i, fun _ _ h => nd.get_inj_iff.1 h,
   fun x =>
    let ⟨i, hl⟩ := List.mem_iff_get.1 (h x)
    ⟨i, hl⟩⟩

variable [DecidableEq α]

/-- If `l` has no duplicates, then `List.get` defines an equivalence between `Fin (length l)` and
the set of elements of `l`. -/
@[simps]
/-
**List.Nodup.getEquiv** 是 Mathlib 中的一个定义，位于命名空间 `List.Nodup`。
形式化陈述：getEquiv (l : List α) (H : Nodup l) : Fin (length l) ≃ { x // x in l } whe
re toFun i
参数：l : List α；H : Nodup l。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l

--- 原说明 ---
If `l` has no duplicates, then `List.get` defines an equivalence between `Fin (l
ength l)` and
the set of elements of `l`.
-/
def getEquiv (l : List α) (H : Nodup l) : Fin (length l) ≃ { x // x ∈ l } where
  toFun i := ⟨get l i, get_mem _ _⟩
  invFun x := ⟨idxOf (↑x) l, idxOf_lt_length_iff.2 x.2⟩
  left_inv i := by simp only [List.get_idxOf, Fin.eta, H]
  right_inv x := by simp

/-- If `l` lists all the elements of `α` without duplicates, then `List.get` defines
an equivalence between `Fin l.length` and `α`.

See `List.Nodup.getBijectionOfForallMemList` for a version without decidable equality. -/
@[simps]
/-
**List.Nodup.getEquivOfForallMemList** 是 Mathlib 中的一个定义，位于命名空间 `List.Nodup`。
形式化陈述：getEquivOfForallMemList (l : List α) (nd : l.Nodup) (h : forall x : α, x i
n l) : Fin l.length ≃ α where toFun i
参数：l : List α；nd : l.Nodup；h : forall x : α, x in l。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `l` lists all the elements of `α` without duplicates, then `List.get` defines
an equivalence between `Fin l.length` and `α`.

See `List.Nodup.getBijectionOfForallMemList` for a version without decidable equ
ality.
-/
def getEquivOfForallMemList (l : List α) (nd : l.Nodup) (h : ∀ x : α, x ∈ l) :
    Fin l.length ≃ α where
  toFun i := l.get i
  invFun a := ⟨_, idxOf_lt_length_iff.2 (h a)⟩
  left_inv i := by simp [nd]
  right_inv a := by simp

end Nodup

section Sorted

/-- Alternative phrasing of `List.Nodup.getEquivOfForallMemList` using `List.count`. -/
@[simps!]
/-
**List.getEquivOfForallCountEqOne** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：getEquivOfForallCountEqOne [DecidableEq α] (l : List α) (h : forall x, l.c
ount x = 1) : Fin l.length ≃ α
参数：l : List α；h : forall x, l.count x = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative phrasing of `List.Nodup.getEquivOfForallMemList` using `List.count`.
-/
def getEquivOfForallCountEqOne [DecidableEq α] (l : List α) (h : ∀ x, l.count x = 1) :
    Fin l.length ≃ α :=
  Nodup.getEquivOfForallMemList _ (List.nodup_iff_count_eq_one.mpr fun _ _ ↦ h _)
    fun _ ↦ List.count_pos_iff.mp <| h _ ▸ Nat.one_pos

variable [Preorder α] {l : List α}

variable [DecidableEq α]

/-- If `l` is a list sorted w.r.t. `(<)`, then `List.get` defines an order isomorphism between
`Fin (length l)` and the set of elements of `l`. -/
/-
**List.SortedLT.getIso** 是 Mathlib 中的一个定义，位于命名空间 `List.SortedLT`。
形式化陈述：{α : Type u_1} → [inst : Preorder α] → [DecidableEq α] → (l : List α) → l.
SortedLT → Fin l.length ≃o { x // x ∈ l }
参数：l : List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `l` is a list sorted w.r.t. `(<)`, then `List.get` defines an order isomorphi
sm between
`Fin (length l)` and the set of elements of `l`.
-/
def SortedLT.getIso (l : List α) (H : SortedLT l) : Fin (length l) ≃o { x // x ∈ l } where
  toEquiv := H.pairwise.nodup.getEquiv l
  map_rel_iff' := H.strictMono_get.le_iff_le

variable (H : SortedLT l) {x : { x // x ∈ l }} {i : Fin l.length}

@[simp]
/-
**List.SortedLT.coe_getIso_apply** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedLT`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : List α} [inst_1 : DecidableEq α]
 (H : l.SortedLT) {i : Fin l.length},   ↑((List.SortedLT.getIso l H) i) = l.get 
i
参数：H : l.SortedLT；(List.SortedLT.getIso l H) i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SortedLT.coe_getIso_apply : (H.getIso l i : α) = get l i :=
  rfl

@[simp]
/-
**List.SortedLT.coe_getIso_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedLT`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : List α} [inst_1 : DecidableEq α]
 (H : l.SortedLT) {x : { x // x ∈ l }},   ↑((List.SortedLT.getIso l H).symm x) =
 List.idxOf (↑x) l
参数：H : l.SortedLT；(List.SortedLT.getIso l H).symm x；↑x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SortedLT.coe_getIso_symm_apply : ((H.getIso l).symm x : ℕ) = idxOf (↑x) l :=
  rfl

end Sorted

section Sublist

/-- If there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`,
then `Sublist l l'`.
-/
/-
**List.sublist_of_orderEmbedding_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublist_of_orderEmbedding_getElem?_eq {l l' : List α} (f : Nat ↪o Nat) (hf
 : forall ix : Nat, l[ix]? = l'[f ix]?) : l <+ l'
参数：f : Nat ↪o Nat；hf : forall ix : Nat, l[ix]? = l'[f ix]?。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`,
then `Sublist l l'`.
-/
theorem sublist_of_orderEmbedding_getElem?_eq {l l' : List α} (f : ℕ ↪o ℕ)
    (hf : ∀ ix : ℕ, l[ix]? = l'[f ix]?) : l <+ l' := by
  induction l generalizing l' f with
  | nil => simp
  | cons hd tl IH => ?_
  have : some hd = l'[f 0]? := by simpa using hf 0
  rw [eq_comm, List.getElem?_eq_some_iff] at this
  obtain ⟨w, h⟩ := this
  let f' : ℕ ↪o ℕ :=
    OrderEmbedding.ofMapLEIff (fun i => f (i + 1) - (f 0 + 1)) fun a b => by
      rw [Nat.sub_le_sub_iff_right, OrderEmbedding.le_iff_le, Nat.succ_le_succ_iff]
      rw [Nat.succ_le_iff, OrderEmbedding.lt_iff_lt]
      exact b.succ_pos
  have : ∀ ix, tl[ix]? = (l'.drop (f 0 + 1))[f' ix]? := by
    intro ix
    rw [List.getElem?_drop, OrderEmbedding.coe_ofMapLEIff, Nat.add_sub_cancel', ← hf]
    · simp only [getElem?_cons_succ]
    rw [Nat.succ_le_iff, OrderEmbedding.lt_iff_lt]
    exact ix.succ_pos
  rw [← List.take_append_drop (f 0 + 1) l', ← List.singleton_append]
  apply List.Sublist.append _ (IH _ this)
  rw [List.singleton_sublist, ← h, l'.getElem_take' _ (Nat.lt_succ_self _)]
  exact List.getElem_mem _

set_option backward.isDefEq.respectTransparency.types false in
/-- A `l : List α` is `Sublist l l'` for `l' : List α` iff
there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
/-
**List.sublist_iff_exists_orderEmbedding_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List
`。
形式化陈述：sublist_iff_exists_orderEmbedding_getElem?_eq {l l' : List α} : l <+ l' ↔ 
exists f : Nat ↪o Nat, forall ix : Nat, l[ix]? = l'[f ix]?
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `l : List α` is `Sublist l l'` for `l' : List α` iff
there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
theorem sublist_iff_exists_orderEmbedding_getElem?_eq {l l' : List α} :
    l <+ l' ↔ ∃ f : ℕ ↪o ℕ, ∀ ix : ℕ, l[ix]? = l'[f ix]? := by
  constructor
  · intro H
    induction H with
    | slnil => simp
    | cons _ _ IH =>
      obtain ⟨f, hf⟩ := IH
      refine ⟨f.trans (OrderEmbedding.ofStrictMono (· + 1) fun _ => by simp), ?_⟩
      simpa using hf
    | cons_cons _ _ IH =>
      obtain ⟨f, hf⟩ := IH
      refine
        ⟨OrderEmbedding.ofMapLEIff (fun ix : ℕ => if ix = 0 then 0 else (f ix.pred).succ) ?_, ?_⟩
      · rintro ⟨_ | a⟩ ⟨_ | b⟩ <;> simp [Nat.succ_le_succ_iff]
      · rintro ⟨_ | i⟩
        · simp
        · simpa using hf _
  · rintro ⟨f, hf⟩
    exact sublist_of_orderEmbedding_getElem?_eq f hf

/-- A `l : List α` is `Sublist l l'` for `l' : List α` iff
there is `f`, an order-preserving embedding of `Fin l.length` into `Fin l'.length` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
/-
**List.sublist_iff_exists_fin_orderEmbedding_get_eq** 是 Mathlib 中的一个定理，位于命名空间 `L
ist`。
形式化陈述：sublist_iff_exists_fin_orderEmbedding_get_eq {l l' : List α} : l <+ l' ↔ e
xists f : Fin l.length ↪o Fin l'.length, forall ix : Fin l.length, l.get ix = l'
.get (f ix)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublist_iff_exists_orderEmbedding_getElem?_eq`：∀ {α : Type u_1} {l 
l' : List α}, l.Sublist l' ↔ ∃ f, ∀ (ix : ℕ), l[ix]? = l'[f ix]?
· 使用定理 `List.getElem?_eq_some_iff`：∀ {α : Type u_1} {i : ℕ} {a : α} {l : List α}
, l[i]? = some a ↔ ∃ (h : i < l.length), l[i] = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `List.getElem?_eq_getElem`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i <
 l.length), l[i]? = some l[i]
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Fin.val_fin_lt`：val_fin_lt {n : Nat} {a b : Fin n} : (a : Nat) < (b : Na
t) ↔ a < b
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c

--- 原说明 ---
A `l : List α` is `Sublist l l'` for `l' : List α` iff
there is `f`, an order-preserving embedding of `Fin l.length` into `Fin l'.lengt
h` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
theorem sublist_iff_exists_fin_orderEmbedding_get_eq {l l' : List α} :
    l <+ l' ↔
      ∃ f : Fin l.length ↪o Fin l'.length,
        ∀ ix : Fin l.length, l.get ix = l'.get (f ix) := by
  rw [sublist_iff_exists_orderEmbedding_getElem?_eq]
  constructor
  · rintro ⟨f, hf⟩
    have h : ∀ {i : ℕ}, i < l.length → f i < l'.length := by
      intro i hi
      specialize hf i
      rw [getElem?_eq_getElem hi, eq_comm, getElem?_eq_some_iff] at hf
      obtain ⟨h, -⟩ := hf
      exact h
    refine ⟨OrderEmbedding.ofMapLEIff (fun ix => ⟨f ix, h ix.is_lt⟩) ?_, ?_⟩
    · simp
    · intro i
      apply Option.some_injective
      simpa [getElem?_eq_getElem i.2, getElem?_eq_getElem (h i.2)] using hf i
  · rintro ⟨f, hf⟩
    refine
      ⟨OrderEmbedding.ofStrictMono (fun i => if hi : i < l.length then f ⟨i, hi⟩ else i + l'.length)
          ?_,
        ?_⟩
    · intro i j h
      dsimp only
      split_ifs with hi hj hj
      · rwa [Fin.val_fin_lt, f.lt_iff_lt]
      · lia
      · exact absurd (h.trans hj) hi
      · simpa using h
    · grind

set_option backward.isDefEq.respectTransparency false in
/-- An element `x : α` of `l : List α` is a duplicate iff it can be found
at two distinct indices `n m : ℕ` inside the list `l`.
-/
/-
**List.duplicate_iff_exists_distinct_get** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：duplicate_iff_exists_distinct_get {l : List α} {x : α} : l.Duplicate x ↔ e
xists (n m : Fin l.length) (_ : n < m), x = l.get n ∧ x = l.get m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.duplicate_iff_two_le_count`：duplicate_iff_two_le_count [DecidableEq
 α] : x in+ l ↔ 2 <= count x l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.replicate_sublist_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α
] {n : ℕ} {a : α} {l : List α},   (List.replicate n a).Sublist l ↔ n ≤ List.coun
t a l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.sublist_iff_exists_fin_orderEmbedding_get_eq`：sublist_iff_exists_fi
n_orderEmbedding_get_eq {l l' : List α} : l <+ l' ↔ exists f : Fin l.length ↪o F
in l'.length, forall ix : Fin l.length,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
· 使用定理 `Nat.zero_lt_one`：0 < 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
An element `x : α` of `l : List α` is a duplicate iff it can be found
at two distinct indices `n m : ℕ` inside the list `l`.
-/
theorem duplicate_iff_exists_distinct_get {l : List α} {x : α} :
    l.Duplicate x ↔
      ∃ (n m : Fin l.length) (_ : n < m),
        x = l.get n ∧ x = l.get m := by
  classical
    rw [duplicate_iff_two_le_count, ← replicate_sublist_iff,
      sublist_iff_exists_fin_orderEmbedding_get_eq]
    constructor
    · rintro ⟨f, hf⟩
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f.lt_iff_lt.2 (Nat.zero_lt_one), ?_⟩
      rw [← hf, ← hf]; simp
    · rintro ⟨n, m, hnm, h, h'⟩
      refine ⟨OrderEmbedding.ofStrictMono (fun i => if (i : ℕ) = 0 then n else m) ?_, ?_⟩
      · rintro ⟨⟨_ | i⟩, hi⟩ ⟨⟨_ | j⟩, hj⟩
        · simp
        · simp [hnm]
        · simp
        · simp only [Nat.lt_succ_iff, Nat.succ_le_succ_iff, replicate, length, Nat.le_zero] at hi hj
          simp [hi, hj]
      · rintro ⟨⟨_ | i⟩, hi⟩
        · simpa using h
        · simpa using h'

end Sublist

end List

