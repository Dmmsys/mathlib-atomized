/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Counting walks of a given length

## Main definitions
- `walkLengthTwoEquivCommonNeighbors`: bijective correspondence between walks of length two
  from `u` to `v` and common neighbours of `u` and `v`. Note that `u` and `v` may be the same.
- `finsetWalkLength`: the `Finset` of length-`n` walks from `u` to `v`.
  This is used to give `{p : G.walk u v | p.length = n}` a `Fintype` instance, and it
  can also be useful as a recursive description of this set when `V` is finite.

TODO: should this be extended further?
-/

@[expose] public section

assert_not_exists Field

open Finset Function

universe u v w

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-
**SimpleGraph.Walk.setOfPred_length_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) (u : V), {p | p.length = 0} = {SimpleGr
aph.Walk.nil}
参数：G : SimpleGraph V；u : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Walk.setOfPred_length_eq_zero (u : V) : {p : G.Walk u u | p.length = 0} = {.nil} := by
  simp [Walk.length_eq_zero_iff, ← Walk.eq_nil_iff_nil]

@[deprecated (since := "2026-07-09")]
alias Walk.setOf_length_eq_zero := Walk.setOfPred_length_eq_zero

@[deprecated (since := "2026-05-12")]
alias set_walk_self_length_zero_eq := Walk.setOfPred_length_eq_zero
/-
**SimpleGraph.Walk.setOfPred_length_eq_zero_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Walk`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {u v : V}, u ≠ v → {p | p.length = 0} =
 ∅
参数：G : SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem (h : forall x, 
x ∉ s) : s = ∅
· 使用定理 `SimpleGraph.Walk.eq_of_length_eq_zero`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.length = 0 → u = v
-/
theorem Walk.setOfPred_length_eq_zero_of_ne {u v : V} (h : u ≠ v) :
    {p : G.Walk u v | p.length = 0} = ∅ :=
  Set.eq_empty_of_forall_notMem (h <| ·.eq_of_length_eq_zero ·)

@[deprecated (since := "2026-07-09")]
alias Walk.setOf_length_eq_zero_of_ne := Walk.setOfPred_length_eq_zero_of_ne

@[deprecated (since := "2026-05-12")]
alias set_walk_length_zero_eq_of_ne := Walk.setOfPred_length_eq_zero_of_ne
/-
**SimpleGraph.Walk.setOfPred_length_eq_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) (u v : V) (n : ℕ),   {p | p.length = n 
+ 1} = ⋃ w, ⋃ (h : G.Adj u w), SimpleGraph.Walk.cons h '' {p' | p'.length = n}
参数：G : SimpleGraph V；u v : V；n : ℕ；h : G.Adj u w。
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
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem Walk.setOfPred_length_eq_add_one (u v : V) (n : ℕ) :
    {p : G.Walk u v | p.length = n + 1} =
      ⋃ (w : V) (h : G.Adj u w), Walk.cons h '' {p' : G.Walk w v | p'.length = n} := by
  ext p
  cases p with
  | nil => simp [eq_comm]
  | cons huw pwv => grind [length_cons, Set.mem_iUnion]

@[deprecated (since := "2026-07-09")]
alias Walk.setOf_length_eq_add_one := Walk.setOfPred_length_eq_add_one

@[deprecated (since := "2026-05-12")]
alias set_walk_length_succ_eq := Walk.setOfPred_length_eq_add_one

/-- Walks of length two from `u` to `v` correspond bijectively to common neighbours of `u` and `v`.
Note that `u` and `v` may be the same. -/
@[simps]
/-
**SimpleGraph.walkLengthTwoEquivCommonNeighbors** 是 Mathlib 中的一个定义，位于命名空间 `Simpl
eGraph`。
形式化陈述：walkLengthTwoEquivCommonNeighbors (u v : V) : {p : G.Walk u v // p.length 
= 2} ≃ G.commonNeighbors u v where toFun p
参数：u v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Walks of length two from `u` to `v` correspond bijectively to common neighbours 
of `u` and `v`.
Note that `u` and `v` may be the same.
-/
def walkLengthTwoEquivCommonNeighbors (u v : V) :
    {p : G.Walk u v // p.length = 2} ≃ G.commonNeighbors u v where
  toFun p := ⟨p.val.snd, match p with
    | ⟨.cons _ (.cons _ .nil), _⟩ => ⟨‹G.Adj u _›, ‹G.Adj _ v›.symm⟩⟩
  invFun w := ⟨w.prop.1.toWalk.concat w.prop.2.symm, rfl⟩
  left_inv | ⟨.cons _ (.cons _ .nil), hp⟩ => by rfl

section LocallyFinite

variable [DecidableEq V] [LocallyFinite G]

set_option backward.isDefEq.respectTransparency.types false in
/-- The `Finset` of length-`n` walks from `u` to `v`.
This is used to give `{p : G.walk u v | p.length = n}` a `Fintype` instance, and it
can also be useful as a recursive description of this set when `V` is finite.

See `SimpleGraph.coe_finsetWalkLength_eq` for the relationship between this `Finset` and
the set of length-`n` walks. -/
/-
**SimpleGraph.finsetWalkLength** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：finsetWalkLength (n : Nat) (u v : V) : Finset (G.Walk u v)
参数：n : Nat；u v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Finset` of length-`n` walks from `u` to `v`.
This is used to give `{p : G.walk u v | p.length = n}` a `Fintype` instance, and
 it
can also be useful as a recursive description of this set when `V` is finite.

See `SimpleGraph.coe_finsetWalkLength_eq` for the relationship between this `Fin
set` and
the set of length-`n` walks.
-/
def finsetWalkLength (n : ℕ) (u v : V) : Finset (G.Walk u v) :=
  match n with
  | 0 =>
    if h : u = v then by
      subst u
      exact {Walk.nil}
    else ∅
  | n + 1 =>
    Finset.univ.biUnion fun (w : G.neighborSet u) =>
      (finsetWalkLength n w v).map ⟨fun p => Walk.cons w.property p, fun _ _ => by simp⟩
/-
**SimpleGraph.coe_finsetWalkLength_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：coe_finsetWalkLength_eq (n : Nat) (u v : V) : (G.finsetWalkLength n u v : 
Set (G.Walk u v)) = {p : G.Walk u v | p.length = n}
参数：n : Nat；u v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `SimpleGraph.Walk.setOfPred_length_eq_add_one`：∀ {V : Type u} (G : Simple
Graph V) (u v : V) (n : ℕ),   {p | p.length = n + 1} = ⋃ w, ⋃ (h : G.Adj u w), S
impleGraph.Walk.cons h '' {p' | p'…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem coe_finsetWalkLength_eq (n : ℕ) (u v : V) :
    (G.finsetWalkLength n u v : Set (G.Walk u v)) = {p : G.Walk u v | p.length = n} := by
  induction n generalizing u v with
  | zero => grind [finsetWalkLength, Walk.eq_nil_iff_nil]
  | succ n ih =>
    simp only [finsetWalkLength, Walk.setOfPred_length_eq_add_one, Finset.coe_biUnion,
      Finset.mem_coe, Finset.mem_univ, Set.iUnion_true, Finset.coe_map, Set.iUnion_coe_set]
    congr!
    grind

variable {G} in
/-
**SimpleGraph.mem_finsetWalkLength_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_finsetWalkLength_iff {n : Nat} {u v : V} {p : G.Walk u v} : p in G.fin
setWalkLength n u v ↔ p.length = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `SimpleGraph.coe_finsetWalkLength_eq`：coe_finsetWalkLength_eq (n : Nat) (
u v : V) : (G.finsetWalkLength n u v : Set (G.Walk u v)) = {p : G.Walk u v | p.l
ength = n}
-/
theorem mem_finsetWalkLength_iff {n : ℕ} {u v : V} {p : G.Walk u v} :
    p ∈ G.finsetWalkLength n u v ↔ p.length = n :=
  Set.ext_iff.mp (G.coe_finsetWalkLength_eq n u v) p

/-- The `Finset` of walks from `u` to `v` with length less than `n`. See `finsetWalkLength` for
context. In particular, we use this definition for `SimpleGraph.Path.instFintype`. -/
/-
**SimpleGraph.finsetWalkLengthLT** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：finsetWalkLengthLT (n : Nat) (u v : V) : Finset (G.Walk u v)
参数：n : Nat；u v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Finset` of walks from `u` to `v` with length less than `n`. See `finsetWalk
Length` for
context. In particular, we use this definition for `SimpleGraph.Path.instFintype
`.
-/
def finsetWalkLengthLT (n : ℕ) (u v : V) : Finset (G.Walk u v) :=
  (Finset.range n).disjiUnion
    (fun l ↦ G.finsetWalkLength l u v)
    (fun l _ l' _ hne _ hsl hsl' p hp ↦
      have hl : p.length = l := mem_finsetWalkLength_iff.mp (hsl hp)
      have hl' : p.length = l' := mem_finsetWalkLength_iff.mp (hsl' hp)
      False.elim <| hne <| hl.symm.trans hl')

set_option backward.isDefEq.respectTransparency.types false in
open Finset in
/-
**SimpleGraph.coe_finsetWalkLengthLT_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：coe_finsetWalkLengthLT_eq (n : Nat) (u v : V) : (G.finsetWalkLengthLT n u 
v : Set (G.Walk u v)) = {p : G.Walk u v | p.length < n}
参数：n : Nat；u v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.disjiUnion_eq_biUnion`：disjiUnion_eq_biUnion (s : Finset α) (f : 
α -> Finset β) (hf) : s.disjiUnion f hf = s.biUnion f
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_finsetWalkLengthLT_eq (n : ℕ) (u v : V) :
    (G.finsetWalkLengthLT n u v : Set (G.Walk u v)) = {p : G.Walk u v | p.length < n} := by
  ext p
  simp [finsetWalkLengthLT, mem_finsetWalkLength_iff]

variable {G} in
/-
**SimpleGraph.mem_finsetWalkLengthLT_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：mem_finsetWalkLengthLT_iff {n : Nat} {u v : V} {p : G.Walk u v} : p in G.f
insetWalkLengthLT n u v ↔ p.length < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `SimpleGraph.coe_finsetWalkLengthLT_eq`：coe_finsetWalkLengthLT_eq (n : Na
t) (u v : V) : (G.finsetWalkLengthLT n u v : Set (G.Walk u v)) = {p : G.Walk u v
 | p.length < n}
-/
theorem mem_finsetWalkLengthLT_iff {n : ℕ} {u v : V} {p : G.Walk u v} :
    p ∈ G.finsetWalkLengthLT n u v ↔ p.length < n :=
  Set.ext_iff.mp (G.coe_finsetWalkLengthLT_eq n u v) p
/-
**SimpleGraph.fintypeSetWalkLength** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：fintypeSetWalkLength (u v : V) (n : Nat) : Fintype {p : G.Walk u v | p.len
gth = n}
参数：u v : V；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeSetWalkLength (u v : V) (n : ℕ) : Fintype {p : G.Walk u v | p.length = n} :=
  Fintype.ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe, coe_finsetWalkLength_eq]
/-
**SimpleGraph.fintypeSubtypeWalkLength** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：fintypeSubtypeWalkLength (u v : V) (n : Nat) : Fintype {p : G.Walk u v // 
p.length = n}
参数：u v : V；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeSubtypeWalkLength (u v : V) (n : ℕ) : Fintype {p : G.Walk u v // p.length = n} :=
  inferInstanceAs <| Fintype {p : G.Walk u v | p.length = n}
/-
**SimpleGraph.set_walk_length_toFinset_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：set_walk_length_toFinset_eq (n : Nat) (u v : V) : {p : G.Walk u v | p.leng
th = n}.toFinset = G.finsetWalkLength n u v
参数：n : Nat；u v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `Finset.toFinset_coe`：Finset.toFinset_coe (s : Finset α) [Fintype (s : Se
t α)] : (s : Set α).toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem set_walk_length_toFinset_eq (n : ℕ) (u v : V) :
    {p : G.Walk u v | p.length = n}.toFinset = G.finsetWalkLength n u v := by
  simp [← coe_finsetWalkLength_eq]

/-- See `SimpleGraph.adjMatrix_pow_apply_eq_card_walk` for the cardinality in terms of the `n`th
power of the adjacency matrix. -/
/-
**SimpleGraph.card_set_walk_length_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：card_set_walk_length_eq (u v : V) (n : Nat) : Fintype.card {p : G.Walk u v
 | p.length = n} = #(G.finsetWalkLength n u v)
参数：u v : V；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `SimpleGraph.coe_finsetWalkLength_eq`：coe_finsetWalkLength_eq (n : Nat) (
u v : V) : (G.finsetWalkLength n u v : Set (G.Walk u v)) = {p : G.Walk u v | p.l
ength = n}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
See `SimpleGraph.adjMatrix_pow_apply_eq_card_walk` for the cardinality in terms 
of the `n`th
power of the adjacency matrix.
-/
theorem card_set_walk_length_eq (u v : V) (n : ℕ) :
    Fintype.card {p : G.Walk u v | p.length = n} = #(G.finsetWalkLength n u v) :=
  Fintype.card_ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe, coe_finsetWalkLength_eq]
/-
**SimpleGraph.fintypeSetWalkLengthLT** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：fintypeSetWalkLengthLT (u v : V) (n : Nat) : Fintype {p : G.Walk u v | p.l
ength < n}
参数：u v : V；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeSetWalkLengthLT (u v : V) (n : ℕ) : Fintype {p : G.Walk u v | p.length < n} :=
  Fintype.ofFinset (G.finsetWalkLengthLT n u v) fun p ↦ by
    rw [← Finset.mem_coe, coe_finsetWalkLengthLT_eq]
/-
**SimpleGraph.fintypeSubtypeWalkLengthLT** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`
。
形式化陈述：fintypeSubtypeWalkLengthLT (u v : V) (n : Nat) : Fintype {p : G.Walk u v /
/ p.length < n}
参数：u v : V；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeSubtypeWalkLengthLT (u v : V) (n : ℕ) : Fintype {p : G.Walk u v // p.length < n} :=
  inferInstanceAs <| Fintype {p : G.Walk u v | p.length < n}
/-
**SimpleGraph.fintypeSetPathLength** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：fintypeSetPathLength (u v : V) (n : Nat) : Fintype {p : G.Walk u v | p.IsP
ath ∧ p.length = n}
参数：u v : V；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeSetPathLength (u v : V) (n : ℕ) :
    Fintype {p : G.Walk u v | p.IsPath ∧ p.length = n} :=
  Fintype.ofFinset {w ∈ G.finsetWalkLength n u v | w.IsPath} <| by
    simp [mem_finsetWalkLength_iff, and_comm]
/-
**SimpleGraph.fintypeSubtypePathLength** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：fintypeSubtypePathLength (u v : V) (n : Nat) : Fintype {p : G.Walk u v // 
p.IsPath ∧ p.length = n}
参数：u v : V；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeSubtypePathLength (u v : V) (n : ℕ) :
    Fintype {p : G.Walk u v // p.IsPath ∧ p.length = n} :=
  inferInstanceAs <| Fintype {p : G.Walk u v | p.IsPath ∧ p.length = n}
/-
**SimpleGraph.fintypeSetPathLengthLT** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：fintypeSetPathLengthLT (u v : V) (n : Nat) : Fintype {p : G.Walk u v | p.I
sPath ∧ p.length < n}
参数：u v : V；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeSetPathLengthLT (u v : V) (n : ℕ) :
    Fintype {p : G.Walk u v | p.IsPath ∧ p.length < n} :=
  Fintype.ofFinset {w ∈ G.finsetWalkLengthLT n u v | w.IsPath} <| by
    simp [mem_finsetWalkLengthLT_iff, and_comm]
/-
**SimpleGraph.fintypeSubtypePathLengthLT** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`
。
形式化陈述：fintypeSubtypePathLengthLT (u v : V) (n : Nat) : Fintype {p : G.Walk u v /
/ p.IsPath ∧ p.length < n}
参数：u v : V；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeSubtypePathLengthLT (u v : V) (n : ℕ) :
    Fintype {p : G.Walk u v // p.IsPath ∧ p.length < n} :=
  inferInstanceAs <| Fintype {p : G.Walk u v | p.IsPath ∧ p.length < n}

end LocallyFinite

section Fintype
variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

/-
**SimpleGraph.Path.instFintype** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Path`。
形式化陈述：{V : Type u} →   (G : SimpleGraph V) → [DecidableEq V] → [Fintype V] → [De
cidableRel G.Adj] → {u v : V} → Fintype (G.Path u v)
参数：G : SimpleGraph V；G.Path u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Path.instFintype {u v : V} : Fintype (G.Path u v) where
  elems := (univ (α := { p : G.Walk u v | p.IsPath ∧ p.length < Fintype.card V })).map
    ⟨fun p ↦ { val := p.val, property := p.prop.left },
     fun _ _ h ↦ SetCoe.ext <| Subtype.mk.injEq .. ▸ h⟩
  complete p := mem_map.mpr ⟨
    ⟨p.val, ⟨p.prop, p.prop.length_lt⟩⟩,
    ⟨mem_univ _, rfl⟩⟩

end Fintype
end SimpleGraph

