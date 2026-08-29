/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Sigma.Basic
public import Batteries.Tactic.Lint.TypeClass

/-!
# A computable model of ZFA without infinity

In this file we define finite hereditary lists. This is useful for calculations in naive set theory.

We distinguish two kinds of ZFA lists:
* Atoms. Directly correspond to an element of the original type.
* Proper ZFA lists. Can be thought of (but are not implemented) as a list of ZFA lists (not
  necessarily proper).

For example, `Lists ℕ` contains stuff like `23`, `[]`, `[37]`, `[1, [[2], 3], 4]`.

## Implementation note

As we want to be able to append both atoms and proper ZFA lists to proper ZFA lists, it's handy that
atoms and proper ZFA lists belong to the same type, even though atoms of `α` could be modelled as
`α` directly. But we don't want to be able to append anything to atoms.

This calls for a two-step definition of ZFA lists:
* First, define ZFA prelists as atoms and proper ZFA prelists. Those proper ZFA prelists are defined
  by inductive appending of (not necessarily proper) ZFA lists.
* Second, define ZFA lists by rubbing out the distinction between atoms and proper lists.

## Main declarations

* `Lists' α false`: Atoms as ZFA prelists. Basically a copy of `α`.
* `Lists' α true`: Proper ZFA prelists. Defined inductively from the empty ZFA prelist
  (`Lists'.nil`) and from appending a ZFA prelist to a proper ZFA prelist (`Lists'.cons a l`).
* `Lists α`: ZFA lists. Sum of the atoms and proper ZFA prelists.
* `Finsets α`: ZFA sets. Defined as `Lists` quotiented by `Lists.Equiv`, the extensional
  equivalence.
-/

@[expose] public section


variable {α : Type*}

/--
Inductive type `Lists'.` / 归纳类型 `Lists'.`

English:
inductive Lists'.{u}
  parameters: (α : Type u)
  constructors (3):
    - atom: α -> Lists' α false
    - nil: Lists' α true
    - cons': {b} : Lists' α b -> Lists' α true -> Lists' α true

中文:
归纳类型 Lists'.{u}
  参数: (α : 类型u)
  构造子 (3 个):
    - atom: α -> Lists' α false
    - nil: Lists' α true
    - cons': {b} : Lists' α b -> Lists' α true -> Lists' α true
-/
inductive Lists'.{u} (α : Type u) : Bool -> Type u
  | atom : α -> Lists' α false
  | nil : Lists' α true
  | cons' {b} : Lists' α b -> Lists' α true -> Lists' α true
  deriving DecidableEq
compile_inductive% Lists'

/--
Definition of `Lists` / `Lists` 的定义

English:
definition Lists
  signature: (α : Type*)
  body: Σ b, Lists' α b

中文:
定义 Lists
  签名: (α : 类型)
  定义体: Σ b, Lists' α b
-/
def Lists (α : Type*) :=
  Σ b, Lists' α b

namespace Lists'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : forall b, Inhabited (Lists' α b)

中文:
实例 [可居
  签名: α] : 对任意 b, 可居 (Lists' α b)
-/
instance [Inhabited α] : forall b, Inhabited (Lists' α b)
  | true => ⟨nil⟩
  | false => ⟨atom default⟩

/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: : Lists α -> Lists' α true -> Lists' α true

中文:
定义 cons
  签名: : Lists α -> Lists' α true -> Lists' α true
-/
def cons : Lists α -> Lists' α true -> Lists' α true
  | ⟨_, a⟩, l => cons' a l

/-- Converts a ZFA prelist to a `List` of ZFA lists. Atoms are sent to `[]`. -/
@[simp]
/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: : forall {b}, Lists' α b -> List (Lists α)

中文:
定义 toList
  签名: : 对任意 {b}, Lists' α b -> 列表 (Lists α)
-/
def toList : forall {b}, Lists' α b -> List (Lists α)
  | _, atom _ => []
  | _, nil => []
  | _, cons' a l => ⟨_, a⟩ :: l.toList

@[simp]
/--
theorem `toList_cons` / 定理 `toList_cons`

English:
theorem toList_cons
  given: (a : Lists α) (l)
  statement: toList (cons a l) = a :: l.toList
  proof: rfl

中文:
定理 toList_cons
  条件: (a : Lists α) (l)
  结论: toList (cons a l) = a :: l.toList
  证明: rfl
-/
theorem toList_cons (a : Lists α) (l) : toList (cons a l) = a :: l.toList := rfl

/-- Converts a `List` of ZFA lists to a proper ZFA prelist. -/
@[simp]
/--
Definition of `ofList` / `ofList` 的定义

English:
definition ofList
  signature: : List (Lists α) -> Lists' α true

中文:
定义 ofList
  签名: : 列表 (Lists α) -> Lists' α true
-/
def ofList : List (Lists α) -> Lists' α true
  | [] => nil
  | a :: l => cons a (ofList l)

@[simp]
/--
theorem `to_ofList` / 定理 `to_ofList`

English:
theorem to_ofList
  given: (l : List (Lists α))
  statement: toList (ofList l) = l
  proof: by induction l <;> simp [*]

@[simp]

中文:
定理 to_ofList
  条件: (l : 列表 (Lists α))
  结论: toList (ofList l) = l
  证明: by induction l <;> simp [*]

@[simp]
-/
theorem to_ofList (l : List (Lists α)) : toList (ofList l) = l := by induction l <;> simp [*]

@[simp]
/--
theorem `of_toList` / 定理 `of_toList`

English:
theorem of_toList
  statement: forall l : Lists' α true, ofList (toList l) = l
  proof: suffices forall (b) (h : true = b) (l : Lists' α b),
      let l' : Lists' α true := h ▸ l
      ofList (toList l') = l'
    from this _ rfl
  fun b h l => by
    induction l with
    | atom => cases h
    | nil => simp
    | cons' b a _ IH => simpa [cons] using IH rfl

中文:
定理 of_toList
  结论: 对任意 l : Lists' α true, ofList (toList l) = l
  证明: suffices forall (b) (h : true = b) (l : Lists' α b),
      let l' : Lists' α true := h ▸ l
      ofList (toList l') = l'
    from this _ rfl
  fun b h l => by
    induction l with
    | atom => cases h
    | nil => simp
    | cons' b a _ IH => simpa [cons] using IH rfl

Depends on / 依赖: ofList, toList
-/
theorem of_toList : forall l : Lists' α true, ofList (toList l) = l :=
  suffices forall (b) (h : true = b) (l : Lists' α b),
      let l' : Lists' α true := h ▸ l
      ofList (toList l') = l'
    from this _ rfl
  fun b h l => by
    induction l with
    | atom => cases h
    | nil => simp
    | cons' b a _ IH => simpa [cons] using IH rfl

/-- Recursion/induction principle for `Lists'.ofList`. -/
@[elab_as_elim]
/--
Definition of `recOfList` / `recOfList` 的定义

English:
definition recOfList
  signature: {motive : Lists' α true -> Sort*} (ofList : forall l, motive (ofList l))
  body: fun l => cast (by simp) ofList (l.toList)

中文:
定义 recOfList
  签名: {motive : Lists' α true -> 类型层*} (ofList : 对任意 l, motive (ofList l))
  定义体: fun l => cast (by simp) ofList (l.toList)

Depends on / 依赖: l.toList, ofList, toList
-/
def recOfList {motive : Lists' α true -> Sort*} (ofList : forall l, motive (ofList l)) : forall l, motive l :=
fun l => cast (by simp) ofList (l.toList)

end Lists'

mutual
/--
Inductive type `Lists.Equiv` / 归纳类型 `Lists.Equiv`

English:
inductive Lists.Equiv
  parameters: : Lists α -> Lists α -> Prop
  constructors (2):
    - refl: (l) : Lists.Equiv l l
    - antisymm: {l₁ l₂ : Lists' α true} : Lists'.Subset l₁ l₂ -> Lists'.Subset l₂ l₁ -> Lists.Equiv ⟨_, l₁⟩ ⟨_, l₂⟩

中文:
归纳类型 Lists.等价
  参数: : Lists α -> Lists α -> 命题
  构造子 (2 个):
    - refl: (l) : Lists.等价 l l
    - antisymm: {l₁ l₂ : Lists' α true} : Lists'.子集 l₁ l₂ -> Lists'.子集 l₂ l₁ -> Lists.等价 ⟨_, l₁⟩ ⟨_, l₂⟩
-/
  inductive Lists.Equiv : Lists α -> Lists α -> Prop
    | refl (l) : Lists.Equiv l l
    | antisymm {l₁ l₂ : Lists' α true} :
      Lists'.Subset l₁ l₂ -> Lists'.Subset l₂ l₁ -> Lists.Equiv ⟨_, l₁⟩ ⟨_, l₂⟩

/--
Inductive type `Lists'.Subset` / 归纳类型 `Lists'.Subset`

English:
inductive Lists'.Subset
  parameters: : Lists' α true -> Lists' α true -> Prop
  constructors (2):
    - nil: {l} : Lists'.Subset Lists'.nil l
    - cons: {a a' l l'} : Lists.Equiv a a' -> a' in Lists'.toList l' -> Lists'.Subset l l' -> Lists'.Subset (Lists'.cons a l) l'

中文:
归纳类型 Lists'.子集
  参数: : Lists' α true -> Lists' α true -> 命题
  构造子 (2 个):
    - nil: {l} : Lists'.子集 Lists'.nil l
    - cons: {a a' l l'} : Lists.等价 a a' -> a' in Lists'.toList l' -> Lists'.子集 l l' -> Lists'.子集 (Lists'.cons a l) l'
-/
  inductive Lists'.Subset : Lists' α true -> Lists' α true -> Prop
    | nil {l} : Lists'.Subset Lists'.nil l
    | cons {a a' l l'} :
      Lists.Equiv a a' ->
        a' in Lists'.toList l' -> Lists'.Subset l l' -> Lists'.Subset (Lists'.cons a l) l'
end

local infixl:50 " ~ " => Lists.Equiv

namespace Lists'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSubset (Lists' α true)
  body: ⟨Lists'.Subset⟩

中文:
实例 :
  签名: HasSubset (Lists' α true)
  定义体: ⟨Lists'.Subset⟩

Depends on / 依赖: Subset
-/
instance : HasSubset (Lists' α true) :=
  ⟨Lists'.Subset⟩

/-- ZFA prelist membership. A ZFA list is in a ZFA prelist if some element of this ZFA prelist is
equivalent as a ZFA list to this ZFA list. -/
instance {b} : Membership (Lists α) (Lists' α b) :=
  ⟨fun l a => exists a' in l.toList, a ~ a'⟩

/--
theorem `mem_def` / 定理 `mem_def`

English:
theorem mem_def
  given: {b a} {l : Lists' α b}
  statement: a in l ↔ exists a' in l.toList, a ~ a'
  proof: Iff.rfl

@[simp]

中文:
定理 mem_def
  条件: {b a} {l : Lists' α b}
  结论: a in l ↔ 存在 a' in l.toList, a ~ a'
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_def {b a} {l : Lists' α b} : a in l ↔ exists a' in l.toList, a ~ a' :=
  Iff.rfl

@[simp]
/--
theorem `mem_cons` / 定理 `mem_cons`

English:
theorem mem_cons
  given: {a y l}
  statement: a in @cons α y l ↔ a ~ y ∨ a in l
  proof: by
  simp [mem_def, or_and_right, exists_or]

中文:
定理 mem_cons
  条件: {a y l}
  结论: a in @cons α y l ↔ a ~ y ∨ a in l
  证明: by
  simp [mem_def, or_and_right, exists_or]

Depends on / 依赖: exists_or, mem_def, or_and_right
-/
theorem mem_cons {a y l} : a in @cons α y l ↔ a ~ y ∨ a in l := by
  simp [mem_def, or_and_right, exists_or]

/--
theorem `cons_subset` / 定理 `cons_subset`

English:
theorem cons_subset
  given: {a} {l₁ l₂ : Lists' α true}
  statement: Lists'.cons a l₁ subseteq l₂ ↔ a in l₂ ∧ l₁ subseteq l₂
  proof: by
  refine ⟨fun h => ?_, fun ⟨⟨a', m, e⟩, s⟩ => Subset.cons e m s⟩
  generalize h' : Lists'.cons a l₁ = l₁' at h
  obtain - | @⟨a', _, _, _, e, m, s⟩ := h
  · cases a
    cases h'
  cases a; cases a'; cases h'; exact ⟨⟨_, m, e⟩, s⟩

中文:
定理 cons_subset
  条件: {a} {l₁ l₂ : Lists' α true}
  结论: Lists'.cons a l₁ subseteq l₂ ↔ a in l₂ ∧ l₁ subseteq l₂
  证明: by
  refine ⟨fun h => ?_, fun ⟨⟨a', m, e⟩, s⟩ => Subset.cons e m s⟩
  generalize h' : Lists'.cons a l₁ = l₁' at h
  obtain - | @⟨a', _, _, _, e, m, s⟩ := h
  · cases a
    cases h'
  cases a; cases a'; cases h'; exact ⟨⟨_, m, e⟩, s⟩

Depends on / 依赖: Subset, Subset.cons, generalize
-/
theorem cons_subset {a} {l₁ l₂ : Lists' α true} : Lists'.cons a l₁ subseteq l₂ ↔ a in l₂ ∧ l₁ subseteq l₂ := by
  refine ⟨fun h => ?_, fun ⟨⟨a', m, e⟩, s⟩ => Subset.cons e m s⟩
  generalize h' : Lists'.cons a l₁ = l₁' at h
  obtain - | @⟨a', _, _, _, e, m, s⟩ := h
  · cases a
    cases h'
  cases a; cases a'; cases h'; exact ⟨⟨_, m, e⟩, s⟩

/--
theorem `ofList_subset` / 定理 `ofList_subset`

English:
theorem ofList_subset
  given: {l₁ l₂ : List (Lists α)} (h : l₁ subseteq l₂)
  proof: by
  induction l₁ with
  | nil => exact Subset.nil
  | cons _ _ l₁_ih =>
    refine Subset.cons (Lists.Equiv.refl _) ?_ (l₁_ih (List.subset_of_cons_subset h))
    simp only [List.cons_subset] at h; simp [h]

@[refl]

中文:
定理 ofList_subset
  条件: {l₁ l₂ : 列表 (Lists α)} (h : l₁ subseteq l₂)
  证明: by
  induction l₁ with
  | nil => exact Subset.nil
  | cons _ _ l₁_ih =>
    refine Subset.cons (Lists.Equiv.refl _) ?_ (l₁_ih (List.subset_of_cons_subset h))
    simp only [List.cons_subset] at h; simp [h]

@[refl]

Depends on / 依赖: List.cons_subset, List.subset_of_cons_subset, Lists.Equiv.refl, Subset, Subset.cons, Subset.nil, cons_subset, subset_of_cons_subset
-/
theorem ofList_subset {l₁ l₂ : List (Lists α)} (h : l₁ subseteq l₂) :
    Lists'.ofList l₁ subseteq Lists'.ofList l₂ := by
  induction l₁ with
  | nil => exact Subset.nil
  | cons _ _ l₁_ih =>
    refine Subset.cons (Lists.Equiv.refl _) ?_ (l₁_ih (List.subset_of_cons_subset h))
    simp only [List.cons_subset] at h; simp [h]

@[refl]
/--
theorem `Subset.refl` / 定理 `Subset.refl`

English:
theorem Subset.refl
  given: {l : Lists' α true}
  statement: l subseteq l
  proof: by
  rw [← Lists'.of_toList l]; exact ofList_subset (List.Subset.refl _)

中文:
定理 子集.refl
  条件: {l : Lists' α true}
  结论: l subseteq l
  证明: by
  rw [← Lists'.of_toList l]; exact ofList_subset (List.Subset.refl _)
-/
theorem Subset.refl {l : Lists' α true} : l subseteq l := by
  rw [← Lists'.of_toList l]; exact ofList_subset (List.Subset.refl _)

/--
theorem `subset_nil` / 定理 `subset_nil`

English:
theorem subset_nil
  given: {l : Lists' α true}
  statement: l subseteq Lists'.nil -> l = Lists'.nil
  proof: by
  rw [← of_toList l]
  induction toList l <;> intro h
  · rfl
  · rcases cons_subset.1 h with ⟨⟨_, ⟨⟩, _⟩, _⟩

中文:
定理 subset_nil
  条件: {l : Lists' α true}
  结论: l subseteq Lists'.nil -> l = Lists'.nil
  证明: by
  rw [← of_toList l]
  induction toList l <;> intro h
  · rfl
  · rcases cons_subset.1 h with ⟨⟨_, ⟨⟩, _⟩, _⟩

Depends on / 依赖: cons_subset, of_toList, toList
-/
theorem subset_nil {l : Lists' α true} : l subseteq Lists'.nil -> l = Lists'.nil := by
  rw [← of_toList l]
  induction toList l <;> intro h
  · rfl
  · rcases cons_subset.1 h with ⟨⟨_, ⟨⟩, _⟩, _⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_of_subset'` / 定理 `mem_of_subset'`

English:
theorem mem_of_subset'
  given: {a}
  statement: forall {l₁ l₂ : Lists' α true} (_ : l₁ subseteq l₂) (_ : a in l₁.toList), a in l₂
  proof: s
    simp only [toList, Sigma.eta, List.mem_cons] at h
    rcases h with (rfl | h)
    · exact ⟨_, m, e⟩
    · exact mem_of_subset' s h

中文:
定理 mem_of_subset'
  条件: {a}
  结论: 对任意 {l₁ l₂ : Lists' α true} (_ : l₁ subseteq l₂) (_ : a in l₁.toList), a in l₂
  证明: s
    simp only [toList, Sigma.eta, List.mem_cons] at h
    rcases h with (rfl | h)
    · exact ⟨_, m, e⟩
    · exact mem_of_subset' s h
-/
theorem mem_of_subset' {a} : forall {l₁ l₂ : Lists' α true} (_ : l₁ subseteq l₂) (_ : a in l₁.toList), a in l₂
  | nil, _, Lists'.Subset.nil, h => by cases h
  | cons' a0 l0, l₂, s, h => by
    obtain - | ⟨e, m, s⟩ := s
    simp only [toList, Sigma.eta, List.mem_cons] at h
    rcases h with (rfl | h)
    · exact ⟨_, m, e⟩
    · exact mem_of_subset' s h

/--
theorem `subset_def` / 定理 `subset_def`

English:
theorem subset_def
  given: {l₁ l₂ : Lists' α true}
  statement: l₁ subseteq l₂ ↔ forall a in l₁.toList, a in l₂
  proof: ⟨fun H _ => mem_of_subset' H, fun H => by
    induction l₁ using recOfList with | _ l₁
    induction l₁ with
    | nil => exact Subset.nil
    | cons h t t_ih =>
      simp only [to_ofList, ofList, toList_cons, List.mem_cons, forall_eq_or_imp] at *
      exact cons_subset.2 ⟨H.1, t_ih H.2⟩⟩

中文:
定理 subset_def
  条件: {l₁ l₂ : Lists' α true}
  结论: l₁ subseteq l₂ ↔ 对任意 a in l₁.toList, a in l₂
  证明: ⟨fun H _ => mem_of_subset' H, fun H => by
    induction l₁ using recOfList with | _ l₁
    induction l₁ with
    | nil => exact Subset.nil
    | cons h t t_ih =>
      simp only [to_ofList, ofList, toList_cons, List.mem_cons, forall_eq_or_imp] at *
      exact cons_subset.2 ⟨H.1, t_ih H.2⟩⟩

Depends on / 依赖: List.mem_cons, Subset, Subset.nil, cons_subset, forall_eq_or_imp, mem_cons, mem_of_subset, ofList, recOfList, t_ih, toList_cons, to_ofList
-/
theorem subset_def {l₁ l₂ : Lists' α true} : l₁ subseteq l₂ ↔ forall a in l₁.toList, a in l₂ :=
  ⟨fun H _ => mem_of_subset' H, fun H => by
    induction l₁ using recOfList with | _ l₁
    induction l₁ with
    | nil => exact Subset.nil
    | cons h t t_ih =>
      simp only [to_ofList, ofList, toList_cons, List.mem_cons, forall_eq_or_imp] at *
      exact cons_subset.2 ⟨H.1, t_ih H.2⟩⟩

end Lists'

namespace Lists

/-- Sends `a : α` to the corresponding atom in `Lists α`. -/
@[match_pattern]
/--
Definition of `atom` / `atom` 的定义

English:
definition atom
  signature: (a : α)
  body: ⟨_, Lists'.atom a⟩

中文:
定义 atom
  签名: (a : α)
  定义体: ⟨_, Lists'.atom a⟩
-/
def atom (a : α) : Lists α :=
  ⟨_, Lists'.atom a⟩

/-- Converts a proper ZFA prelist to a ZFA list. -/
@[match_pattern]
/--
Definition of `of'` / `of'` 的定义

English:
definition of'
  signature: (l : Lists' α true)
  body: ⟨_, l⟩

中文:
定义 of'
  签名: (l : Lists' α true)
  定义体: ⟨_, l⟩
-/
def of' (l : Lists' α true) : Lists α :=
  ⟨_, l⟩

/-- Converts a ZFA list to a `List` of ZFA lists. Atoms are sent to `[]`. -/
@[simp]
/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: : Lists α -> List (Lists α)

中文:
定义 toList
  签名: : Lists α -> 列表 (Lists α)
-/
def toList : Lists α -> List (Lists α)
  | ⟨_, l⟩ => l.toList

/--
Definition of `IsList` / `IsList` 的定义

English:
definition IsList
  signature: (l : Lists α)
  body: l.1

中文:
定义 IsList
  签名: (l : Lists α)
  定义体: l.1
-/
def IsList (l : Lists α) : Prop :=
  l.1

/--
Definition of `ofList` / `ofList` 的定义

English:
definition ofList
  signature: (l : List (Lists α))
  body: of' (Lists'.ofList l)

中文:
定义 ofList
  签名: (l : 列表 (Lists α))
  定义体: of' (Lists'.ofList l)

Depends on / 依赖: ofList
-/
def ofList (l : List (Lists α)) : Lists α :=
  of' (Lists'.ofList l)

/--
theorem `isList_toList` / 定理 `isList_toList`

English:
theorem isList_toList
  given: (l : List (Lists α))
  statement: IsList (ofList l)
  proof: Eq.refl _

中文:
定理 isList_toList
  条件: (l : 列表 (Lists α))
  结论: IsList (ofList l)
  证明: Eq.refl _

Depends on / 依赖: Eq.refl
-/
theorem isList_toList (l : List (Lists α)) : IsList (ofList l) :=
  Eq.refl _

/--
theorem `to_ofList` / 定理 `to_ofList`

English:
theorem to_ofList
  given: (l : List (Lists α))
  statement: toList (ofList l) = l
  proof: by simp [ofList, of']

中文:
定理 to_ofList
  条件: (l : 列表 (Lists α))
  结论: toList (ofList l) = l
  证明: by simp [ofList, of']

Depends on / 依赖: ofList
-/
theorem to_ofList (l : List (Lists α)) : toList (ofList l) = l := by simp [ofList, of']

set_option backward.isDefEq.respectTransparency false in
/--
theorem `of_toList` / 定理 `of_toList`

English:
theorem of_toList
  statement: forall {l : Lists α}, IsList l -> ofList (toList l) = l

中文:
定理 of_toList
  结论: 对任意 {l : Lists α}, IsList l -> ofList (toList l) = l
-/
theorem of_toList : forall {l : Lists α}, IsList l -> ofList (toList l) = l
  | ⟨true, l⟩, _ => by simp_all [ofList, of']

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Lists α)
  body: ⟨of' Lists'.nil⟩

中文:
实例 :
  签名: 可居 (Lists α)
  定义体: ⟨of' Lists'.nil⟩
-/
instance : Inhabited (Lists α) :=
  ⟨of' Lists'.nil⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : DecidableEq (Lists α)
  body: inferInstanceAs DecidableEq (Sigma _)

中文:
实例 [DecidableEq
  签名: α] : DecidableEq (Lists α)
  定义体: inferInstanceAs DecidableEq (Sigma _)

Depends on / 依赖: DecidableEq
-/
instance [DecidableEq α] : DecidableEq (Lists α) := inferInstanceAs DecidableEq (Sigma _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SizeOf
  signature: α] : SizeOf (Lists α)
  body: inferInstanceAs SizeOf (Sigma _)

中文:
实例 [SizeOf
  签名: α] : SizeOf (Lists α)
  定义体: inferInstanceAs SizeOf (Sigma _)

Depends on / 依赖: SizeOf
-/
instance [SizeOf α] : SizeOf (Lists α) := inferInstanceAs SizeOf (Sigma _)

/--
Definition of `inductionMut` / `inductionMut` 的定义

English:
definition inductionMut
  signature: (C : Lists α -> Sort*) (D : Lists' α true -> Sort*)
  body: by
  suffices forall {b} (l : Lists' α b),
      PProd (C ⟨_, l⟩)
        (match b, l with
        | true, l => D l
        | false, _ => PUnit)
    ⟨fun ⟨b, l⟩ => (this _).1, fun l => (this l).2⟩
  intro b l
  induction l with
  | atom => exact ⟨C0 _, ⟨⟩⟩
  | nil => exact ⟨C1 _ D0, D0⟩
  | cons' a l IH₁ IH =>
    have : D (Lists'.cons' a l) := D1 ⟨_, _⟩ _ IH₁.1 IH.2
    exact ⟨C1 _ this, this⟩

中文:
定义 inductionMut
  签名: (C : Lists α -> 类型层*) (D : Lists' α true -> 类型层*)
  定义体: by
  suffices forall {b} (l : Lists' α b),
      PProd (C ⟨_, l⟩)
        (match b, l with
        | true, l => D l
        | false, _ => PUnit)
    ⟨fun ⟨b, l⟩ => (this _).1, fun l => (this l).2⟩
  intro b l
  induction l with
  | atom => exact ⟨C0 _, ⟨⟩⟩
  | nil => exact ⟨C1 _ D0, D0⟩
  | cons' a l IH₁ IH =>
    have : D (Lists'.cons' a l) := D1 ⟨_, _⟩ _ IH₁.1 IH.2
    exact ⟨C1 _ this, this⟩
-/
def inductionMut (C : Lists α -> Sort*) (D : Lists' α true -> Sort*)
    (C0 : forall a, C (atom a)) (C1 : forall l, D l -> C (of' l))
    (D0 : D Lists'.nil) (D1 : forall a l, C a -> D l -> D (Lists'.cons a l)) :
    PProd (forall l, C l) (forall l, D l) := by
  suffices forall {b} (l : Lists' α b),
      PProd (C ⟨_, l⟩)
        (match b, l with
        | true, l => D l
        | false, _ => PUnit)
    ⟨fun ⟨b, l⟩ => (this _).1, fun l => (this l).2⟩
  intro b l
  induction l with
  | atom => exact ⟨C0 _, ⟨⟩⟩
  | nil => exact ⟨C1 _ D0, D0⟩
  | cons' a l IH₁ IH =>
    have : D (Lists'.cons' a l) := D1 ⟨_, _⟩ _ IH₁.1 IH.2
    exact ⟨C1 _ this, this⟩

/--
Definition of `mem` / `mem` 的定义

English:
definition mem
  signature: (a : Lists α)

中文:
定义 mem
  签名: (a : Lists α)
-/
def mem (a : Lists α) : Lists α -> Prop
  | ⟨false, _⟩ => False
  | ⟨_, l⟩ => a in l

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership (Lists α) (Lists α)
  body: mem l ls

中文:
实例 :
  签名: Membership (Lists α) (Lists α)
  定义体: mem l ls
-/
instance : Membership (Lists α) (Lists α) where
  mem ls l := mem l ls

/--
theorem `isList_of_mem` / 定理 `isList_of_mem`

English:
theorem isList_of_mem
  given: {a : Lists α}
  statement: forall {l : Lists α}, a in l -> IsList l

中文:
定理 isList_of_mem
  条件: {a : Lists α}
  结论: 对任意 {l : Lists α}, a in l -> IsList l
-/
theorem isList_of_mem {a : Lists α} : forall {l : Lists α}, a in l -> IsList l
  | ⟨_, Lists'.nil⟩, _ => rfl
  | ⟨_, Lists'.cons' _ _⟩, _ => rfl

/--
theorem `Equiv.antisymm_iff` / 定理 `Equiv.antisymm_iff`

English:
theorem Equiv.antisymm_iff
  given: {l₁ l₂ : Lists' α true}
  statement: of' l₁ ~ of' l₂ ↔ l₁ subseteq l₂ ∧ l₂ subseteq l₁
  proof: by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => Equiv.antisymm h₁ h₂⟩
  obtain - | ⟨h₁, h₂⟩ := h
  · simp [Lists'.Subset.refl]
  · exact ⟨h₁, h₂⟩

中文:
定理 等价.antisymm_iff
  条件: {l₁ l₂ : Lists' α true}
  结论: of' l₁ ~ of' l₂ ↔ l₁ subseteq l₂ ∧ l₂ subseteq l₁
  证明: by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => Equiv.antisymm h₁ h₂⟩
  obtain - | ⟨h₁, h₂⟩ := h
  · simp [Lists'.Subset.refl]
  · exact ⟨h₁, h₂⟩

Depends on / 依赖: Equiv.antisymm, Subset, Subset.refl, antisymm
-/
theorem Equiv.antisymm_iff {l₁ l₂ : Lists' α true} : of' l₁ ~ of' l₂ ↔ l₁ subseteq l₂ ∧ l₂ subseteq l₁ := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => Equiv.antisymm h₁ h₂⟩
  obtain - | ⟨h₁, h₂⟩ := h
  · simp [Lists'.Subset.refl]
  · exact ⟨h₁, h₂⟩

attribute [refl] Equiv.refl

/--
theorem `equiv_atom` / 定理 `equiv_atom`

English:
theorem equiv_atom
  given: {a} {l : Lists α}
  statement: atom a ~ l ↔ atom a = l
  proof: ⟨fun h => by cases h; rfl, fun h => h ▸ Equiv.refl _⟩

@[symm]

中文:
定理 equiv_atom
  条件: {a} {l : Lists α}
  结论: atom a ~ l ↔ atom a = l
  证明: ⟨fun h => by cases h; rfl, fun h => h ▸ Equiv.refl _⟩

@[symm]

Depends on / 依赖: Equiv.refl
-/
theorem equiv_atom {a} {l : Lists α} : atom a ~ l ↔ atom a = l :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ Equiv.refl _⟩

@[symm]
/--
theorem `Equiv.symm` / 定理 `Equiv.symm`

English:
theorem Equiv.symm
  given: {l₁ l₂ : Lists α} (h : l₁ ~ l₂)
  statement: l₂ ~ l₁
  proof: by
  obtain - | ⟨h₁, h₂⟩ := h <;> [rfl; exact Equiv.antisymm h₂ h₁]

中文:
定理 等价.symm
  条件: {l₁ l₂ : Lists α} (h : l₁ ~ l₂)
  结论: l₂ ~ l₁
  证明: by
  obtain - | ⟨h₁, h₂⟩ := h <;> [rfl; exact Equiv.antisymm h₂ h₁]
-/
theorem Equiv.symm {l₁ l₂ : Lists α} (h : l₁ ~ l₂) : l₂ ~ l₁ := by
  obtain - | ⟨h₁, h₂⟩ := h <;> [rfl; exact Equiv.antisymm h₂ h₁]

/--
theorem `Equiv.trans` / 定理 `Equiv.trans`

English:
theorem Equiv.trans
  statement: forall {l₁ l₂ l₃ : Lists α}, l₁ ~ l₂ -> l₂ ~ l₃ -> l₁ ~ l₃
  proof: by
  let trans := fun l₁ : Lists α => forall ⦃l₂ l₃⦄, l₁ ~ l₂ -> l₂ ~ l₃ -> l₁ ~ l₃
  suffices PProd (forall l₁, trans l₁) (forall (l : Lists' α true), forall l' in l.toList, trans l') by exact this.1
  apply inductionMut
  · intro a l₂ l₃ h₁ h₂
    rwa [← equiv_atom.1 h₁] at h₂
  · intro l₁ IH l₂ l₃ h₁ h₂
    obtain - | l₂ := id h₁
    · exact h₂
    obtain - | l₃ := id h₂
    · exact h₁
    obtain ⟨hl₁, hr₁⟩ := Equiv.antisymm_iff.1 h₁
    obtain ⟨hl₂, hr₂⟩ := Equiv.antisymm_iff.1 h₂
    apply Equiv.antisymm_iff.2; constructor <;> apply Lists'.subset_def.2
    · intro a₁ m₁
      rcases Lists'.mem_of_subset' hl₁ m₁ with ⟨a₂, m₂, e₁₂⟩
      rcases Lists'.mem_of_subset' hl₂ m₂ with ⟨a₃, m₃, e₂₃⟩
      exact ⟨a₃, m₃, IH _ m₁ e₁₂ e₂₃⟩
    · intro a₃ m₃
      rcases Lists'.mem_of_subset' hr₂ m₃ with ⟨a₂, m₂, e₃₂⟩
      rcases Lists'.mem_of_subset' hr₁ m₂ with ⟨a₁, m₁, e₂₁⟩
      exact ⟨a₁, m₁, (IH _ m₁ e₂₁.symm e₃₂.symm).symm⟩
  · rintro _ ⟨⟩
  · intro a l IH₁ IH₂
    simpa using ⟨IH₁, IH₂⟩

中文:
定理 等价.trans
  结论: 对任意 {l₁ l₂ l₃ : Lists α}, l₁ ~ l₂ -> l₂ ~ l₃ -> l₁ ~ l₃
  证明: by
  let trans := fun l₁ : Lists α => forall ⦃l₂ l₃⦄, l₁ ~ l₂ -> l₂ ~ l₃ -> l₁ ~ l₃
  suffices PProd (forall l₁, trans l₁) (forall (l : Lists' α true), forall l' in l.toList, trans l') by exact this.1
  apply inductionMut
  · intro a l₂ l₃ h₁ h₂
    rwa [← equiv_atom.1 h₁] at h₂
  · intro l₁ IH l₂ l₃ h₁ h₂
    obtain - | l₂ := id h₁
    · exact h₂
    obtain - | l₃ := id h₂
    · exact h₁
    obtain ⟨hl₁, hr₁⟩ := Equiv.antisymm_iff.1 h₁
    obtain ⟨hl₂, hr₂⟩ := Equiv.antisymm_iff.1 h₂
    apply Equiv.antisymm_iff.2; constructor <;> apply Lists'.subset_def.2
    · intro a₁ m₁
      rcases Lists'.mem_of_subset' hl₁ m₁ with ⟨a₂, m₂, e₁₂⟩
      rcases Lists'.mem_of_subset' hl₂ m₂ with ⟨a₃, m₃, e₂₃⟩
      exact ⟨a₃, m₃, IH _ m₁ e₁₂ e₂₃⟩
    · intro a₃ m₃
      rcases Lists'.mem_of_subset' hr₂ m₃ with ⟨a₂, m₂, e₃₂⟩
      rcases Lists'.mem_of_subset' hr₁ m₂ with ⟨a₁, m₁, e₂₁⟩
      exact ⟨a₁, m₁, (IH _ m₁ e₂₁.symm e₃₂.symm).symm⟩
  · rintro _ ⟨⟩
  · intro a l IH₁ IH₂
    simpa using ⟨IH₁, IH₂⟩
-/
theorem Equiv.trans : forall {l₁ l₂ l₃ : Lists α}, l₁ ~ l₂ -> l₂ ~ l₃ -> l₁ ~ l₃ := by
  let trans := fun l₁ : Lists α => forall ⦃l₂ l₃⦄, l₁ ~ l₂ -> l₂ ~ l₃ -> l₁ ~ l₃
  suffices PProd (forall l₁, trans l₁) (forall (l : Lists' α true), forall l' in l.toList, trans l') by exact this.1
  apply inductionMut
  · intro a l₂ l₃ h₁ h₂
    rwa [← equiv_atom.1 h₁] at h₂
  · intro l₁ IH l₂ l₃ h₁ h₂
    obtain - | l₂ := id h₁
    · exact h₂
    obtain - | l₃ := id h₂
    · exact h₁
    obtain ⟨hl₁, hr₁⟩ := Equiv.antisymm_iff.1 h₁
    obtain ⟨hl₂, hr₂⟩ := Equiv.antisymm_iff.1 h₂
    apply Equiv.antisymm_iff.2; constructor <;> apply Lists'.subset_def.2
    · intro a₁ m₁
      rcases Lists'.mem_of_subset' hl₁ m₁ with ⟨a₂, m₂, e₁₂⟩
      rcases Lists'.mem_of_subset' hl₂ m₂ with ⟨a₃, m₃, e₂₃⟩
      exact ⟨a₃, m₃, IH _ m₁ e₁₂ e₂₃⟩
    · intro a₃ m₃
      rcases Lists'.mem_of_subset' hr₂ m₃ with ⟨a₂, m₂, e₃₂⟩
      rcases Lists'.mem_of_subset' hr₁ m₂ with ⟨a₁, m₁, e₂₁⟩
      exact ⟨a₁, m₁, (IH _ m₁ e₂₁.symm e₃₂.symm).symm⟩
  · rintro _ ⟨⟩
  · intro a l IH₁ IH₂
    simpa using ⟨IH₁, IH₂⟩

/--
Instance `instSetoidLists` / 实例 `instSetoidLists`

English:
instance instSetoidLists
  signature: : Setoid (Lists α)
  body: ⟨(· ~ ·), Equiv.refl, @Equiv.symm _, @Equiv.trans _⟩

中文:
实例 instSetoidLists
  签名: : 集合等价关系 (Lists α)
  定义体: ⟨(· ~ ·), Equiv.refl, @Equiv.symm _, @Equiv.trans _⟩

Depends on / 依赖: Equiv.refl, Equiv.symm, Equiv.trans
-/
instance instSetoidLists : Setoid (Lists α) :=
  ⟨(· ~ ·), Equiv.refl, @Equiv.symm _, @Equiv.trans _⟩

section Decidable

/--
theorem `sizeof_pos` / 定理 `sizeof_pos`

English:
theorem sizeof_pos
  given: {b} (l : Lists' α b)
  statement: 0 < SizeOf.sizeOf l
  proof: by
  cases l <;> simp only [Lists'.atom.sizeOf_spec, Lists'.nil.sizeOf_spec, Lists'.cons'.sizeOf_spec,
    true_or, add_pos_iff, zero_lt_one]

中文:
定理 sizeof_pos
  条件: {b} (l : Lists' α b)
  结论: 0 < SizeOf.sizeOf l
  证明: by
  cases l <;> simp only [Lists'.atom.sizeOf_spec, Lists'.nil.sizeOf_spec, Lists'.cons'.sizeOf_spec,
    true_or, add_pos_iff, zero_lt_one]

Depends on / 依赖: add_pos_iff, atom.sizeOf_spec, nil.sizeOf_spec, sizeOf_spec, true_or, zero_lt_one
-/
theorem sizeof_pos {b} (l : Lists' α b) : 0 < SizeOf.sizeOf l := by
  cases l <;> simp only [Lists'.atom.sizeOf_spec, Lists'.nil.sizeOf_spec, Lists'.cons'.sizeOf_spec,
    true_or, add_pos_iff, zero_lt_one]

/--
theorem `lt_sizeof_cons'` / 定理 `lt_sizeof_cons'`

English:
theorem lt_sizeof_cons'
  given: {b} (a : Lists' α b) (l)
  proof: by
  simp only [Sigma.mk.sizeOf_spec, Lists'.cons'.sizeOf_spec, lt_add_iff_pos_right]
  apply sizeof_pos

中文:
定理 lt_sizeof_cons'
  条件: {b} (a : Lists' α b) (l)
  证明: by
  simp only [Sigma.mk.sizeOf_spec, Lists'.cons'.sizeOf_spec, lt_add_iff_pos_right]
  apply sizeof_pos

Depends on / 依赖: Sigma.mk.sizeOf_spec, lt_add_iff_pos_right, sizeOf_spec, sizeof_pos
-/
theorem lt_sizeof_cons' {b} (a : Lists' α b) (l) :
    SizeOf.sizeOf (⟨b, a⟩ : Lists α) < SizeOf.sizeOf (Lists'.cons' a l) := by
  simp only [Sigma.mk.sizeOf_spec, Lists'.cons'.sizeOf_spec, lt_add_iff_pos_right]
  apply sizeof_pos

variable [DecidableEq α]

set_option backward.isDefEq.respectTransparency false in
mutual
  @[instance_reducible]
/--
Definition of `Equiv.decidable` / `Equiv.decidable` 的定义

English:
definition Equiv.decidable
  signature: : forall l₁ l₂ : Lists α, Decidable (l₁ ~ l₂)
  body: have : SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf (⟨true, l₁⟩ : Lists α) + SizeOf.sizeOf (⟨true, l₂⟩ : Lists α) := by
          decreasing_tactic
        Subset.decidable l₁ l₂
      haveI : Decidable (l₂ subseteq l₁) :=
        have : SizeOf.sizeOf l₂ + SizeOf.sizeOf l₁ <
            SizeOf.sizeOf (⟨true, l₁⟩ : Lists α) + SizeOf.sizeOf (⟨true, l₂⟩ : Lists α) := by
          decreasing_tactic
        Subset.decidable l₂ l₁
      exact decidable_of_iff' _ Equiv.antisymm_iff
  termination_by x y => sizeOf x + sizeOf y
  @[instance_reducible]

中文:
定义 等价.decidable
  签名: : 对任意 l₁ l₂ : Lists α, 可判定 (l₁ ~ l₂)
  定义体: have : SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf (⟨true, l₁⟩ : Lists α) + SizeOf.sizeOf (⟨true, l₂⟩ : Lists α) := by
          decreasing_tactic
        Subset.decidable l₁ l₂
      haveI : Decidable (l₂ subseteq l₁) :=
        have : SizeOf.sizeOf l₂ + SizeOf.sizeOf l₁ <
            SizeOf.sizeOf (⟨true, l₁⟩ : Lists α) + SizeOf.sizeOf (⟨true, l₂⟩ : Lists α) := by
          decreasing_tactic
        Subset.decidable l₂ l₁
      exact decidable_of_iff' _ Equiv.antisymm_iff
  termination_by x y => sizeOf x + sizeOf y
  @[instance_reducible]

Depends on / 依赖: Decidable, Equiv.antisymm_iff, SizeOf, SizeOf.sizeOf, Subset, Subset.decidable, antisymm_iff, decidable, decidable_of_iff, decreasing_tactic, instance_reducible, sizeOf, subseteq, termination_by
-/
  def Equiv.decidable : forall l₁ l₂ : Lists α, Decidable (l₁ ~ l₂)
    | ⟨false, l₁⟩, ⟨false, l₂⟩ =>
decidable_of_iff' (l₁ = l₂) by
        cases l₁
        apply equiv_atom.trans
        simp only [atom]
        constructor <;> (rintro ⟨rfl⟩; rfl)
| ⟨false, l₁⟩, ⟨true, l₂⟩ => isFalse by rintro ⟨⟩
| ⟨true, l₁⟩, ⟨false, l₂⟩ => isFalse by rintro ⟨⟩
    | ⟨true, l₁⟩, ⟨true, l₂⟩ => by
      haveI : Decidable (l₁ subseteq l₂) :=
        have : SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf (⟨true, l₁⟩ : Lists α) + SizeOf.sizeOf (⟨true, l₂⟩ : Lists α) := by
          decreasing_tactic
        Subset.decidable l₁ l₂
      haveI : Decidable (l₂ subseteq l₁) :=
        have : SizeOf.sizeOf l₂ + SizeOf.sizeOf l₁ <
            SizeOf.sizeOf (⟨true, l₁⟩ : Lists α) + SizeOf.sizeOf (⟨true, l₂⟩ : Lists α) := by
          decreasing_tactic
        Subset.decidable l₂ l₁
      exact decidable_of_iff' _ Equiv.antisymm_iff
  termination_by x y => sizeOf x + sizeOf y
  @[instance_reducible]
/--
Definition of `Subset.decidable` / `Subset.decidable` 的定义

English:
definition Subset.decidable
  signature: : forall l₁ l₂ : Lists' α true, Decidable (l₁ subseteq l₂)
  body: have : sizeOf (⟨b, a⟩ : Lists α) < 1 + 1 + sizeOf a + sizeOf l₁ := by simp [sizeof_pos]
        mem.decidable ⟨b, a⟩ l₂
      haveI :=
        have : SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf (Lists'.cons' a l₁) + SizeOf.sizeOf l₂ := by
          decreasing_tactic
        Subset.decidable l₁ l₂
      exact decidable_of_iff' _ (@Lists'.cons_subset _ ⟨_, _⟩ _ _)
  termination_by x y => sizeOf x + sizeOf y
  @[instance_reducible]

中文:
定义 子集.decidable
  签名: : 对任意 l₁ l₂ : Lists' α true, 可判定 (l₁ subseteq l₂)
  定义体: have : sizeOf (⟨b, a⟩ : Lists α) < 1 + 1 + sizeOf a + sizeOf l₁ := by simp [sizeof_pos]
        mem.decidable ⟨b, a⟩ l₂
      haveI :=
        have : SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf (Lists'.cons' a l₁) + SizeOf.sizeOf l₂ := by
          decreasing_tactic
        Subset.decidable l₁ l₂
      exact decidable_of_iff' _ (@Lists'.cons_subset _ ⟨_, _⟩ _ _)
  termination_by x y => sizeOf x + sizeOf y
  @[instance_reducible]

Depends on / 依赖: SizeOf, SizeOf.sizeOf, Subset, Subset.decidable, cons_subset, decidable, decidable_of_iff, decreasing_tactic, instance_reducible, mem.decidable, sizeOf, sizeof_pos, termination_by
-/
  def Subset.decidable : forall l₁ l₂ : Lists' α true, Decidable (l₁ subseteq l₂)
    | Lists'.nil, _ => isTrue Lists'.Subset.nil
    | @Lists'.cons' _ b a l₁, l₂ => by
      haveI :=
        have : sizeOf (⟨b, a⟩ : Lists α) < 1 + 1 + sizeOf a + sizeOf l₁ := by simp [sizeof_pos]
        mem.decidable ⟨b, a⟩ l₂
      haveI :=
        have : SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf (Lists'.cons' a l₁) + SizeOf.sizeOf l₂ := by
          decreasing_tactic
        Subset.decidable l₁ l₂
      exact decidable_of_iff' _ (@Lists'.cons_subset _ ⟨_, _⟩ _ _)
  termination_by x y => sizeOf x + sizeOf y
  @[instance_reducible]
/--
Definition of `mem.decidable` / `mem.decidable` 的定义

English:
definition mem.decidable
  signature: : forall (a : Lists α) (l : Lists' α true), Decidable (a in l)
  body: have : sizeOf (⟨_, b⟩ : Lists α) < 1 + 1 + sizeOf b + sizeOf l₂ := by simp [sizeof_pos]
        Equiv.decidable a ⟨_, b⟩
      haveI :=
        have :
          SizeOf.sizeOf a + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf a + SizeOf.sizeOf (Lists'.cons' b l₂) := by
          decreasing_tactic
        mem.decidable a l₂
      refine decidable_of_iff' (a ~ ⟨_, b⟩ ∨ a in l₂) ?_
      rw [← Lists'.mem_cons]; rfl
  termination_by x y => sizeOf x + sizeOf y

中文:
定义 mem.decidable
  签名: : 对任意 (a : Lists α) (l : Lists' α true), 可判定 (a in l)
  定义体: have : sizeOf (⟨_, b⟩ : Lists α) < 1 + 1 + sizeOf b + sizeOf l₂ := by simp [sizeof_pos]
        Equiv.decidable a ⟨_, b⟩
      haveI :=
        have :
          SizeOf.sizeOf a + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf a + SizeOf.sizeOf (Lists'.cons' b l₂) := by
          decreasing_tactic
        mem.decidable a l₂
      refine decidable_of_iff' (a ~ ⟨_, b⟩ ∨ a in l₂) ?_
      rw [← Lists'.mem_cons]; rfl
  termination_by x y => sizeOf x + sizeOf y

Depends on / 依赖: CauSeq, CauSeq.IsComplete, IsComplete, completeSpace_of_cauSeq_isComplete
-/
  def mem.decidable : forall (a : Lists α) (l : Lists' α true), Decidable (a in l)
| a, Lists'.nil => isFalse by rintro ⟨_, ⟨⟩, _⟩
    | a, Lists'.cons' b l₂ => by
      haveI :=
        have : sizeOf (⟨_, b⟩ : Lists α) < 1 + 1 + sizeOf b + sizeOf l₂ := by simp [sizeof_pos]
        Equiv.decidable a ⟨_, b⟩
      haveI :=
        have :
          SizeOf.sizeOf a + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf a + SizeOf.sizeOf (Lists'.cons' b l₂) := by
          decreasing_tactic
        mem.decidable a l₂
      refine decidable_of_iff' (a ~ ⟨_, b⟩ ∨ a in l₂) ?_
      rw [← Lists'.mem_cons]; rfl
  termination_by x y => sizeOf x + sizeOf y
end

attribute [instance] Equiv.decidable Subset.decidable mem.decidable

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableRel ((· ≈ ·) : Lists α -> Lists α -> Prop)
  body: Lists.Equiv.decidable

中文:
实例 :
  签名: DecidableRel ((· ≈ ·) : Lists α -> Lists α -> 命题)
  定义体: Lists.Equiv.decidable

Depends on / 依赖: Lists.Equiv.decidable, decidable
-/
instance : DecidableRel ((· ≈ ·) : Lists α -> Lists α -> Prop) :=
  Lists.Equiv.decidable

end Decidable

end Lists

namespace Lists'

/--
theorem `mem_equiv_left` / 定理 `mem_equiv_left`

English:
theorem mem_equiv_left
  given: {l : Lists' α true}
  statement: forall {a a'}, a ~ a' -> (a in l ↔ a' in l)
  proof: suffices forall {a a'}, a ~ a' -> a in l -> a' in l from fun e => ⟨this e, this e.symm⟩
  fun e₁ ⟨_, m₃, e₂⟩ => ⟨_, m₃, e₁.symm.trans e₂⟩

中文:
定理 mem_equiv_left
  条件: {l : Lists' α true}
  结论: 对任意 {a a'}, a ~ a' -> (a in l ↔ a' in l)
  证明: suffices forall {a a'}, a ~ a' -> a in l -> a' in l from fun e => ⟨this e, this e.symm⟩
  fun e₁ ⟨_, m₃, e₂⟩ => ⟨_, m₃, e₁.symm.trans e₂⟩

Depends on / 依赖: e.symm, symm.trans
-/
theorem mem_equiv_left {l : Lists' α true} : forall {a a'}, a ~ a' -> (a in l ↔ a' in l) :=
  suffices forall {a a'}, a ~ a' -> a in l -> a' in l from fun e => ⟨this e, this e.symm⟩
  fun e₁ ⟨_, m₃, e₂⟩ => ⟨_, m₃, e₁.symm.trans e₂⟩

/--
theorem `mem_of_subset` / 定理 `mem_of_subset`

English:
theorem mem_of_subset
  given: {a} {l₁ l₂ : Lists' α true} (s : l₁ subseteq l₂)
  statement: a in l₁ -> a in l₂

中文:
定理 mem_of_subset
  条件: {a} {l₁ l₂ : Lists' α true} (s : l₁ subseteq l₂)
  结论: a in l₁ -> a in l₂
-/
theorem mem_of_subset {a} {l₁ l₂ : Lists' α true} (s : l₁ subseteq l₂) : a in l₁ -> a in l₂
  | ⟨_, m, e⟩ => (mem_equiv_left e).2 (mem_of_subset' s m)

/--
theorem `Subset.trans` / 定理 `Subset.trans`

English:
theorem Subset.trans
  given: {l₁ l₂ l₃ : Lists' α true} (h₁ : l₁ subseteq l₂) (h₂ : l₂ subseteq l₃)
  statement: l₁ subseteq l₃
  proof: subset_def.2 fun _ m₁ => mem_of_subset h₂ mem_of_subset' h₁ m₁

中文:
定理 子集.trans
  条件: {l₁ l₂ l₃ : Lists' α true} (h₁ : l₁ subseteq l₂) (h₂ : l₂ subseteq l₃)
  结论: l₁ subseteq l₃
  证明: subset_def.2 fun _ m₁ => mem_of_subset h₂ mem_of_subset' h₁ m₁
-/
theorem Subset.trans {l₁ l₂ l₃ : Lists' α true} (h₁ : l₁ subseteq l₂) (h₂ : l₂ subseteq l₃) : l₁ subseteq l₃ :=
subset_def.2 fun _ m₁ => mem_of_subset h₂ mem_of_subset' h₁ m₁

end Lists'

/--
Definition of `Finsets` / `Finsets` 的定义

English:
definition Finsets
  signature: (α : Type*)
  body: Quotient (@Lists.instSetoidLists α)

中文:
定义 Finsets
  签名: (α : 类型)
  定义体: Quotient (@Lists.instSetoidLists α)

Depends on / 依赖: Lists.instSetoidLists, Quotient, instSetoidLists
-/
def Finsets (α : Type*) :=
  Quotient (@Lists.instSetoidLists α)

namespace Finsets

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmptyCollection (Finsets α)
  body: ⟨⟦Lists.of' Lists'.nil⟧⟩

中文:
实例 :
  签名: EmptyCollection (Finsets α)
  定义体: ⟨⟦Lists.of' Lists'.nil⟧⟩

Depends on / 依赖: Lists.of
-/
instance : EmptyCollection (Finsets α) :=
  ⟨⟦Lists.of' Lists'.nil⟧⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Finsets α)
  body: ⟨∅⟩

中文:
实例 :
  签名: 可居 (Finsets α)
  定义体: ⟨∅⟩
-/
instance : Inhabited (Finsets α) :=
  ⟨∅⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : DecidableEq (Finsets α)
  body: inferInstanceAs DecidableEq (Quotient Lists.instSetoidLists)

中文:
实例 [DecidableEq
  签名: α] : DecidableEq (Finsets α)
  定义体: inferInstanceAs DecidableEq (Quotient Lists.instSetoidLists)

Depends on / 依赖: DecidableEq, Lists.instSetoidLists, Quotient, instSetoidLists
-/
instance [DecidableEq α] : DecidableEq (Finsets α) :=
inferInstanceAs DecidableEq (Quotient Lists.instSetoidLists)

end Finsets
