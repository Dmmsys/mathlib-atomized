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

/--
Definition of `DegLex` / `DegLex` 的定义

English:
definition DegLex
  signature: (α : Type*)
  body: α

中文:
定义 DegLex
  签名: (α : 类型)
  定义体: α
-/
def DegLex (α : Type*) := α

variable {α : Type*}

/--
Definition of `toDegLex` / `toDegLex` 的定义

English:
definition toDegLex
  signature: : α ≃ DegLex α
  body: Equiv.refl _

中文:
定义 toDegLex
  签名: : α ≃ DegLex α
  定义体: Equiv.refl _
-/
@[match_pattern] def toDegLex : α ≃ DegLex α := Equiv.refl _

/--
theorem `toDegLex_injective` / 定理 `toDegLex_injective`

English:
theorem toDegLex_injective
  statement: Function.Injective (toDegLex (α := α))
  proof: fun _ _ => _root_.id

中文:
定理 toDegLex_injective
  结论: 函数.单射 (toDegLex (α := α))
  证明: fun _ _ => _root_.id

Depends on / 依赖: _root_, _root_.id
-/
theorem toDegLex_injective : Function.Injective (toDegLex (α := α)) := fun _ _ => _root_.id

/--
theorem `toDegLex_inj` / 定理 `toDegLex_inj`

English:
theorem toDegLex_inj
  given: {a b : α}
  statement: toDegLex a = toDegLex b ↔ a = b
  proof: Iff.rfl

中文:
定理 toDegLex_inj
  条件: {a b : α}
  结论: toDegLex a = toDegLex b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toDegLex_inj {a b : α} : toDegLex a = toDegLex b ↔ a = b := Iff.rfl

/--
Definition of `ofDegLex` / `ofDegLex` 的定义

English:
definition ofDegLex
  signature: : DegLex α ≃ α
  body: Equiv.refl _

中文:
定义 ofDegLex
  签名: : DegLex α ≃ α
  定义体: Equiv.refl _
-/
@[match_pattern] def ofDegLex : DegLex α ≃ α := Equiv.refl _

/--
theorem `ofDegLex_injective` / 定理 `ofDegLex_injective`

English:
theorem ofDegLex_injective
  statement: Function.Injective (ofDegLex (α := α))
  proof: fun _ _ => _root_.id

中文:
定理 ofDegLex_injective
  结论: 函数.单射 (ofDegLex (α := α))
  证明: fun _ _ => _root_.id

Depends on / 依赖: _root_, _root_.id
-/
theorem ofDegLex_injective : Function.Injective (ofDegLex (α := α)) := fun _ _ => _root_.id

/--
theorem `ofDegLex_inj` / 定理 `ofDegLex_inj`

English:
theorem ofDegLex_inj
  given: {a b : DegLex α}
  statement: ofDegLex a = ofDegLex b ↔ a = b
  proof: Iff.rfl

中文:
定理 ofDegLex_inj
  条件: {a b : DegLex α}
  结论: ofDegLex a = ofDegLex b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ofDegLex_inj {a b : DegLex α} : ofDegLex a = ofDegLex b ↔ a = b := Iff.rfl

/--
theorem `ofDegLex_symm_eq` / 定理 `ofDegLex_symm_eq`

English:
theorem ofDegLex_symm_eq
  statement: (@ofDegLex α).symm = toDegLex
  proof: rfl

中文:
定理 ofDegLex_symm_eq
  结论: (@ofDegLex α).symm = toDegLex
  证明: rfl
-/
@[simp] theorem ofDegLex_symm_eq : (@ofDegLex α).symm = toDegLex := rfl

/--
theorem `toDegLex_symm_eq` / 定理 `toDegLex_symm_eq`

English:
theorem toDegLex_symm_eq
  statement: (@toDegLex α).symm = ofDegLex
  proof: rfl

中文:
定理 toDegLex_symm_eq
  结论: (@toDegLex α).symm = ofDegLex
  证明: rfl
-/
@[simp] theorem toDegLex_symm_eq : (@toDegLex α).symm = ofDegLex := rfl

/--
theorem `ofDegLex_toDegLex` / 定理 `ofDegLex_toDegLex`

English:
theorem ofDegLex_toDegLex
  given: (a : α)
  statement: ofDegLex (toDegLex a) = a
  proof: rfl

中文:
定理 ofDegLex_toDegLex
  条件: (a : α)
  结论: ofDegLex (toDegLex a) = a
  证明: rfl
-/
@[simp] theorem ofDegLex_toDegLex (a : α) : ofDegLex (toDegLex a) = a := rfl

/--
theorem `toDegLex_ofDegLex` / 定理 `toDegLex_ofDegLex`

English:
theorem toDegLex_ofDegLex
  given: (a : DegLex α)
  statement: toDegLex (ofDegLex a) = a
  proof: rfl

中文:
定理 toDegLex_ofDegLex
  条件: (a : DegLex α)
  结论: toDegLex (ofDegLex a) = a
  证明: rfl
-/
@[simp] theorem toDegLex_ofDegLex (a : DegLex α) : toDegLex (ofDegLex a) = a := rfl

/-- A recursor for `DegLex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/--
Definition of `DegLex.rec` / `DegLex.rec` 的定义

English:
definition DegLex.rec
  signature: {β : DegLex α -> Sort*} (h : forall a, β (toDegLex a))
  body: fun a => h (ofDegLex a)

中文:
定义 DegLex.rec
  签名: {β : DegLex α -> 类型层*} (h : 对任意 a, β (toDegLex a))
  定义体: fun a => h (ofDegLex a)
-/
protected def DegLex.rec {β : DegLex α -> Sort*} (h : forall a, β (toDegLex a)) :
    forall a, β a := fun a => h (ofDegLex a)

/--
lemma `DegLex.forall_iff` / 引理 `DegLex.forall_iff`

English:
lemma DegLex.forall_iff
  given: {p : DegLex α -> Prop}
  statement: (forall a, p a) ↔ forall a, p (toDegLex a)
  proof: Iff.rfl

中文:
引理 DegLex.对任意_iff
  条件: {p : DegLex α -> 命题}
  结论: (对任意 a, p a) ↔ 对任意 a, p (toDegLex a)
  证明: Iff.rfl
-/
@[simp] lemma DegLex.forall_iff {p : DegLex α -> Prop} : (forall a, p a) ↔ forall a, p (toDegLex a) := Iff.rfl
/--
lemma `DegLex.exists_iff` / 引理 `DegLex.exists_iff`

English:
lemma DegLex.exists_iff
  given: {p : DegLex α -> Prop}
  statement: (exists a, p a) ↔ exists a, p (toDegLex a)
  proof: Iff.rfl

中文:
引理 DegLex.存在_iff
  条件: {p : DegLex α -> 命题}
  结论: (存在 a, p a) ↔ 存在 a, p (toDegLex a)
  证明: Iff.rfl
-/
@[simp] lemma DegLex.exists_iff {p : DegLex α -> Prop} : (exists a, p a) ↔ exists a, p (toDegLex a) := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: α] :
  body: ofDegLex.addCommMonoid

中文:
实例 [加法交换幺半群
  签名: α] :
  定义体: ofDegLex.addCommMonoid

Depends on / 依赖: addCommMonoid, ofDegLex, ofDegLex.addCommMonoid
-/
noncomputable instance [AddCommMonoid α] :
    AddCommMonoid (DegLex α) := ofDegLex.addCommMonoid

/--
theorem `toDegLex_add` / 定理 `toDegLex_add`

English:
theorem toDegLex_add
  given: [AddCommMonoid α] (a b : α)
  proof: rfl

中文:
定理 toDegLex_add
  条件: [加法交换幺半群 α] (a b : α)
  证明: rfl
-/
theorem toDegLex_add [AddCommMonoid α] (a b : α) :
    toDegLex (a + b) = toDegLex a + toDegLex b := rfl

/--
theorem `ofDegLex_add` / 定理 `ofDegLex_add`

English:
theorem ofDegLex_add
  given: [AddCommMonoid α] (a b : DegLex α)
  proof: rfl

中文:
定理 ofDegLex_add
  条件: [加法交换幺半群 α] (a b : DegLex α)
  证明: rfl
-/
theorem ofDegLex_add [AddCommMonoid α] (a b : DegLex α) :
    ofDegLex (a + b) = ofDegLex a + ofDegLex b := rfl

namespace Finsupp

open scoped Function in -- required for scoped `on` notation
/--
Definition of `DegLex` / `DegLex` 的定义

English:
definition DegLex
  signature: (r : α -> α -> Prop) (s : Nat -> Nat -> Prop)
  body: (Prod.Lex s (Finsupp.Lex r s)) on (fun x => (x.degree, x))

中文:
定义 DegLex
  签名: (r : α -> α -> 命题) (s : 自然数 -> 自然数 -> 命题)
  定义体: (Prod.Lex s (Finsupp.Lex r s)) on (fun x => (x.degree, x))
-/
protected def DegLex (r : α -> α -> Prop) (s : Nat -> Nat -> Prop) :
    (α ->₀ Nat) -> (α ->₀ Nat) -> Prop :=
  (Prod.Lex s (Finsupp.Lex r s)) on (fun x => (x.degree, x))

/--
theorem `degLex_def` / 定理 `degLex_def`

English:
theorem degLex_def
  given: {r : α -> α -> Prop} {s : Nat -> Nat -> Prop} {a b : α ->₀ Nat}
  proof: Iff.rfl

中文:
定理 degLex_def
  条件: {r : α -> α -> 命题} {s : 自然数 -> 自然数 -> 命题} {a b : α ->₀ 自然数}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem degLex_def {r : α -> α -> Prop} {s : Nat -> Nat -> Prop} {a b : α ->₀ Nat} :
    Finsupp.DegLex r s a b ↔ Prod.Lex s (Finsupp.Lex r s) (a.degree, a) (b.degree, b) :=
  Iff.rfl

namespace DegLex

/--
theorem `wellFounded` / 定理 `wellFounded`

English:
theorem wellFounded
  proof: by
  have wft := WellFounded.prod_lex hs (Finsupp.Lex.wellFounded' hs0 hs hr)
  rw [← Set.wellFoundedOn_univ] at wft
  unfold Finsupp.DegLex
  rw [← Set.wellFoundedOn_range]
  exact Set.WellFoundedOn.mono wft (le_refl _) (fun _ _ => trivial)

中文:
定理 wellFounded
  证明: by
  have wft := WellFounded.prod_lex hs (Finsupp.Lex.wellFounded' hs0 hs hr)
  rw [← Set.wellFoundedOn_univ] at wft
  unfold Finsupp.DegLex
  rw [← Set.wellFoundedOn_range]
  exact Set.WellFoundedOn.mono wft (le_refl _) (fun _ _ => trivial)

Depends on / 依赖: DegLex, Finsupp, Finsupp.DegLex, Finsupp.Lex.wellFounded, Set.WellFoundedOn.mono, Set.wellFoundedOn_range, Set.wellFoundedOn_univ, WellFounded, WellFounded.prod_lex, WellFoundedOn, le_refl, prod_lex, wellFounded, wellFoundedOn_range, wellFoundedOn_univ
-/
theorem wellFounded
    {r : α -> α -> Prop} [Std.Trichotomous r] (hr : WellFounded (Function.swap r))
    {s : Nat -> Nat -> Prop} (hs : WellFounded s) (hs0 : forall ⦃n⦄, ¬ s n 0) :
    WellFounded (Finsupp.DegLex r s) := by
  have wft := WellFounded.prod_lex hs (Finsupp.Lex.wellFounded' hs0 hs hr)
  rw [← Set.wellFoundedOn_univ] at wft
  unfold Finsupp.DegLex
  rw [← Set.wellFoundedOn_range]
  exact Set.WellFoundedOn.mono wft (le_refl _) (fun _ _ => trivial)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: α] : LT (DegLex (α ->₀ Nat))
  body: ⟨fun f g => Finsupp.DegLex (· < ·) (· < ·) (ofDegLex f) (ofDegLex g)⟩

中文:
实例 [LT
  签名: α] : LT (DegLex (α ->₀ 自然数))
  定义体: ⟨fun f g => Finsupp.DegLex (· < ·) (· < ·) (ofDegLex f) (ofDegLex g)⟩

Depends on / 依赖: DegLex, Finsupp, Finsupp.DegLex, ofDegLex
-/
instance [LT α] : LT (DegLex (α ->₀ Nat)) :=
  ⟨fun f g => Finsupp.DegLex (· < ·) (· < ·) (ofDegLex f) (ofDegLex g)⟩

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: [LT α] {a b : DegLex (α ->₀ Nat)}
  proof: Iff.rfl

中文:
定理 lt_def
  条件: [LT α] {a b : DegLex (α ->₀ 自然数)}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem lt_def [LT α] {a b : DegLex (α ->₀ Nat)} :
    a < b ↔ (toLex ((ofDegLex a).degree, toLex (ofDegLex a))) <
        (toLex ((ofDegLex b).degree, toLex (ofDegLex b))) :=
  Iff.rfl

/--
theorem `lt_iff` / 定理 `lt_iff`

English:
theorem lt_iff
  given: [LT α] {a b : DegLex (α ->₀ Nat)}
  proof: by
  simp [lt_def, Prod.Lex.toLex_lt_toLex]

中文:
定理 lt_iff
  条件: [LT α] {a b : DegLex (α ->₀ 自然数)}
  证明: by
  simp [lt_def, Prod.Lex.toLex_lt_toLex]

Depends on / 依赖: Prod.Lex.toLex_lt_toLex, lt_def, toLex_lt_toLex
-/
theorem lt_iff [LT α] {a b : DegLex (α ->₀ Nat)} :
    a < b ↔ (ofDegLex a).degree < (ofDegLex b).degree ∨
    (((ofDegLex a).degree = (ofDegLex b).degree) ∧ toLex (ofDegLex a) < toLex (ofDegLex b)) := by
  simp [lt_def, Prod.Lex.toLex_lt_toLex]

variable [LinearOrder α]

/--
Instance `isStrictOrder` / 实例 `isStrictOrder`

English:
instance isStrictOrder
  signature: : IsStrictOrder (DegLex (α ->₀ Nat)) (· < ·) where
  body: fun a => by simp [lt_def]
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

中文:
实例 isStrictOrder
  签名: : 是Strict序 (DegLex (α ->₀ 自然数)) (· < ·) where
  定义体: fun a => by simp [lt_def]
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

Depends on / 依赖: lt_def
-/
instance isStrictOrder : IsStrictOrder (DegLex (α ->₀ Nat)) (· < ·) where
  irrefl := fun a => by simp [lt_def]
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder (DegLex (α ->₀ Nat))
  body: fast_instance% LinearOrder.lift'
    (fun (f : DegLex (α ->₀ Nat)) => toLex ((ofDegLex f).degree, toLex (ofDegLex f)))
    (fun f g => by simp)

中文:
实例 :
  签名: 线性序 (DegLex (α ->₀ 自然数))
  定义体: fast_instance% LinearOrder.lift'
    (fun (f : DegLex (α ->₀ Nat)) => toLex ((ofDegLex f).degree, toLex (ofDegLex f)))
    (fun f g => by simp)

Depends on / 依赖: DegLex, LinearOrder, LinearOrder.lift, degree, fast_instance, ofDegLex
-/
noncomputable instance : LinearOrder (DegLex (α ->₀ Nat)) :=
  fast_instance% LinearOrder.lift'
    (fun (f : DegLex (α ->₀ Nat)) => toLex ((ofDegLex f).degree, toLex (ofDegLex f)))
    (fun f g => by simp)

/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  given: {x y : DegLex (α ->₀ Nat)}
  proof: by
  simp only [le_iff_eq_or_lt, lt_iff, EmbeddingLike.apply_eq_iff_eq]
  by_cases h : x = y
  · simp [h]
  · by_cases k : (ofDegLex x).degree < (ofDegLex y).degree
    · simp [k]
    · simp only [h, k, false_or]

中文:
定理 le_iff
  条件: {x y : DegLex (α ->₀ 自然数)}
  证明: by
  simp only [le_iff_eq_or_lt, lt_iff, EmbeddingLike.apply_eq_iff_eq]
  by_cases h : x = y
  · simp [h]
  · by_cases k : (ofDegLex x).degree < (ofDegLex y).degree
    · simp [k]
    · simp only [h, k, false_or]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, apply_eq_iff_eq, degree, false_or, le_iff_eq_or_lt, lt_iff, ofDegLex
-/
theorem le_iff {x y : DegLex (α ->₀ Nat)} :
    x <= y ↔ (ofDegLex x).degree < (ofDegLex y).degree ∨
      (ofDegLex x).degree = (ofDegLex y).degree ∧ toLex (ofDegLex x) <= toLex (ofDegLex y) := by
  simp only [le_iff_eq_or_lt, lt_iff, EmbeddingLike.apply_eq_iff_eq]
  by_cases h : x = y
  · simp [h]
  · by_cases k : (ofDegLex x).degree < (ofDegLex y).degree
    · simp [k]
    · simp only [h, k, false_or]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedCancelAddMonoid (DegLex (α ->₀ Nat))
  body: by
    rw [le_iff] at h ⊢
    simpa only [ofDegLex_add, map_add, add_lt_add_iff_left, add_right_inj, toLex_add,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [le_iff] at h ⊢
    simpa [ofDegLex_add, map_add] using h

中文:
实例 :
  签名: 是OrderedCancelAdd幺半群 (DegLex (α ->₀ 自然数))
  定义体: by
    rw [le_iff] at h ⊢
    simpa only [ofDegLex_add, map_add, add_lt_add_iff_left, add_right_inj, toLex_add,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [le_iff] at h ⊢
    simpa [ofDegLex_add, map_add] using h

Depends on / 依赖: add_le_add_iff_left, add_le_add_left, add_lt_add_iff_left, add_right_inj, le_iff, map_add, ofDegLex_add, toLex_add
-/
instance : IsOrderedCancelAddMonoid (DegLex (α ->₀ Nat)) where
  le_of_add_le_add_left a b c h := by
    rw [le_iff] at h ⊢
    simpa only [ofDegLex_add, map_add, add_lt_add_iff_left, add_right_inj, toLex_add,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [le_iff] at h ⊢
    simpa [ofDegLex_add, map_add] using h

/--
theorem `single_strictAnti` / 定理 `single_strictAnti`

English:
theorem single_strictAnti
  statement: StrictAnti (fun (a : α) => toDegLex (single a 1))
  proof: by
  intro _ _ h
  simp only [lt_iff, ofDegLex_toDegLex, degree_single, lt_self_iff_false, Lex.single_lt_iff, h,
    and_self, or_true]

中文:
定理 single_strictAnti
  结论: 严格递减 (fun (a : α) => toDegLex (single a 1))
  证明: by
  intro _ _ h
  simp only [lt_iff, ofDegLex_toDegLex, degree_single, lt_self_iff_false, Lex.single_lt_iff, h,
    and_self, or_true]

Depends on / 依赖: Lex.single_lt_iff, and_self, degree_single, lt_iff, lt_self_iff_false, ofDegLex_toDegLex, or_true, single_lt_iff
-/
theorem single_strictAnti : StrictAnti (fun (a : α) => toDegLex (single a 1)) := by
  intro _ _ h
  simp only [lt_iff, ofDegLex_toDegLex, degree_single, lt_self_iff_false, Lex.single_lt_iff, h,
    and_self, or_true]

/--
theorem `single_antitone` / 定理 `single_antitone`

English:
theorem single_antitone
  statement: Antitone (fun (a : α) => toDegLex (single a 1))
  proof: single_strictAnti.antitone

中文:
定理 single_antitone
  结论: 递减 (fun (a : α) => toDegLex (single a 1))
  证明: single_strictAnti.antitone

Depends on / 依赖: antitone, single_strictAnti, single_strictAnti.antitone
-/
theorem single_antitone : Antitone (fun (a : α) => toDegLex (single a 1)) :=
  single_strictAnti.antitone

/--
theorem `single_lt_iff` / 定理 `single_lt_iff`

English:
theorem single_lt_iff
  given: {a b : α}
  proof: single_strictAnti.lt_iff_gt

中文:
定理 single_lt_iff
  条件: {a b : α}
  证明: single_strictAnti.lt_iff_gt

Depends on / 依赖: lt_iff_gt, single_strictAnti, single_strictAnti.lt_iff_gt
-/
theorem single_lt_iff {a b : α} :
    toDegLex (Finsupp.single b 1) < toDegLex (Finsupp.single a 1) ↔ a < b :=
  single_strictAnti.lt_iff_gt

/--
theorem `single_le_iff` / 定理 `single_le_iff`

English:
theorem single_le_iff
  given: {a b : α}
  proof: single_strictAnti.le_iff_ge

中文:
定理 single_le_iff
  条件: {a b : α}
  证明: single_strictAnti.le_iff_ge

Depends on / 依赖: le_iff_ge, single_strictAnti, single_strictAnti.le_iff_ge
-/
theorem single_le_iff {a b : α} :
    toDegLex (Finsupp.single b 1) <= toDegLex (Finsupp.single a 1) ↔ a <= b :=
  single_strictAnti.le_iff_ge

/--
theorem `monotone_degree` / 定理 `monotone_degree`

English:
theorem monotone_degree
  proof: by
  intro x y
  rw [le_iff]
  rintro (h | h)
  · apply le_of_lt h
  · apply le_of_eq h.1

中文:
定理 monotone_degree
  证明: by
  intro x y
  rw [le_iff]
  rintro (h | h)
  · apply le_of_lt h
  · apply le_of_eq h.1

Depends on / 依赖: le_iff, le_of_eq, le_of_lt
-/
theorem monotone_degree :
    Monotone (fun (x : DegLex (α ->₀ Nat)) => (ofDegLex x).degree) := by
  intro x y
  rw [le_iff]
  rintro (h | h)
  · apply le_of_lt h
  · apply le_of_eq h.1

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: : OrderBot (DegLex (α ->₀ Nat)) where
  body: toDegLex (0 : α ->₀ Nat)
  bot_le x := by
    simp only [le_iff, ofDegLex_toDegLex, toLex_zero, map_zero]
    rcases eq_zero_or_pos (ofDegLex x).degree with (h | h)
    · simp only [h, lt_self_iff_false, true_and, false_or]
      exact bot_le
    · simp [h]

中文:
实例 orderBot
  签名: : 有底序 (DegLex (α ->₀ 自然数)) where
  定义体: toDegLex (0 : α ->₀ Nat)
  bot_le x := by
    simp only [le_iff, ofDegLex_toDegLex, toLex_zero, map_zero]
    rcases eq_zero_or_pos (ofDegLex x).degree with (h | h)
    · simp only [h, lt_self_iff_false, true_and, false_or]
      exact bot_le
    · simp [h]

Depends on / 依赖: toDegLex
-/
noncomputable instance orderBot : OrderBot (DegLex (α ->₀ Nat)) where
  bot := toDegLex (0 : α ->₀ Nat)
  bot_le x := by
    simp only [le_iff, ofDegLex_toDegLex, toLex_zero, map_zero]
    rcases eq_zero_or_pos (ofDegLex x).degree with (h | h)
    · simp only [h, lt_self_iff_false, true_and, false_or]
      exact bot_le
    · simp [h]

/--
Instance `wellFoundedLT` / 实例 `wellFoundedLT`

English:
instance wellFoundedLT
  signature: [WellFoundedGT α]
  body: ⟨wellFounded wellFounded_gt wellFounded_lt fun _ => not_lt_zero⟩

中文:
实例 wellFoundedLT
  签名: [WellFoundedGT α]
  定义体: ⟨wellFounded wellFounded_gt wellFounded_lt fun _ => not_lt_zero⟩

Depends on / 依赖: not_lt_zero, wellFounded, wellFounded_gt, wellFounded_lt
-/
instance wellFoundedLT [WellFoundedGT α] : WellFoundedLT (DegLex (α ->₀ Nat)) :=
  ⟨wellFounded wellFounded_gt wellFounded_lt fun _ => not_lt_zero⟩

end DegLex

end Finsupp

namespace MonomialOrder

open Finsupp

variable {σ : Type*} [LinearOrder σ] [WellFoundedGT σ]

/--
Definition of `degLex` / `degLex` 的定义

English:
definition degLex
  signature: :
  body: DegLex (σ ->₀ Nat)
  toSyn := { toEquiv := toDegLex, map_add' := toDegLex_add }
  toSyn_monotone a b h := by
    simp only [AddEquiv.coe_mk, DegLex.le_iff, ofDegLex_toDegLex]
    by_cases! ha : a.degree < b.degree
    · exact Or.inl ha
    · refine Or.inr ⟨le_antisymm ?_ ha, toLex_monotone h⟩
      rw [← add_tsub_cancel_of_le h]; rw [map_add]
      exact Nat.le_add_right a.degree (b - a).degree

中文:
定义 degLex
  签名: :
  定义体: DegLex (σ ->₀ Nat)
  toSyn := { toEquiv := toDegLex, map_add' := toDegLex_add }
  toSyn_monotone a b h := by
    simp only [AddEquiv.coe_mk, DegLex.le_iff, ofDegLex_toDegLex]
    by_cases! ha : a.degree < b.degree
    · exact Or.inl ha
    · refine Or.inr ⟨le_antisymm ?_ ha, toLex_monotone h⟩
      rw [← add_tsub_cancel_of_le h]; rw [map_add]
      exact Nat.le_add_right a.degree (b - a).degree

Depends on / 依赖: DegLex
-/
noncomputable def degLex :
    MonomialOrder σ where
  syn := DegLex (σ ->₀ Nat)
  toSyn := { toEquiv := toDegLex, map_add' := toDegLex_add }
  toSyn_monotone a b h := by
    simp only [AddEquiv.coe_mk, DegLex.le_iff, ofDegLex_toDegLex]
    by_cases! ha : a.degree < b.degree
    · exact Or.inl ha
    · refine Or.inr ⟨le_antisymm ?_ ha, toLex_monotone h⟩
      rw [← add_tsub_cancel_of_le h]; rw [map_add]
      exact Nat.le_add_right a.degree (b - a).degree

/--
theorem `degLex_le_iff` / 定理 `degLex_le_iff`

English:
theorem degLex_le_iff
  given: {a b : σ ->₀ Nat}
  proof: Iff.rfl

中文:
定理 degLex_le_iff
  条件: {a b : σ ->₀ 自然数}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl, intros
-/
theorem degLex_le_iff {a b : σ ->₀ Nat} :
    a ≼[degLex] b ↔ toDegLex a <= toDegLex b :=
  Iff.rfl

/--
theorem `degLex_lt_iff` / 定理 `degLex_lt_iff`

English:
theorem degLex_lt_iff
  given: {a b : σ ->₀ Nat}
  proof: Iff.rfl

中文:
定理 degLex_lt_iff
  条件: {a b : σ ->₀ 自然数}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem degLex_lt_iff {a b : σ ->₀ Nat} :
    a ≺[degLex] b ↔ toDegLex a < toDegLex b :=
  Iff.rfl

/--
theorem `degLex_single_le_iff` / 定理 `degLex_single_le_iff`

English:
theorem degLex_single_le_iff
  given: {a b : σ}
  proof: by
  rw [MonomialOrder.degLex_le_iff]; rw [DegLex.single_le_iff]

中文:
定理 degLex_single_le_iff
  条件: {a b : σ}
  证明: by
  rw [MonomialOrder.degLex_le_iff]; rw [DegLex.single_le_iff]

Depends on / 依赖: DegLex, DegLex.single_le_iff, MonomialOrder, MonomialOrder.degLex_le_iff, degLex_le_iff, single_le_iff
-/
theorem degLex_single_le_iff {a b : σ} :
    single a 1 ≼[degLex] single b 1 ↔ b <= a := by
  rw [MonomialOrder.degLex_le_iff]; rw [DegLex.single_le_iff]

/--
theorem `degLex_single_lt_iff` / 定理 `degLex_single_lt_iff`

English:
theorem degLex_single_lt_iff
  given: {a b : σ}
  proof: by
  rw [MonomialOrder.degLex_lt_iff]; rw [DegLex.single_lt_iff]

中文:
定理 degLex_single_lt_iff
  条件: {a b : σ}
  证明: by
  rw [MonomialOrder.degLex_lt_iff]; rw [DegLex.single_lt_iff]

Depends on / 依赖: DegLex, DegLex.single_lt_iff, MonomialOrder, MonomialOrder.degLex_lt_iff, degLex_lt_iff, single_lt_iff
-/
theorem degLex_single_lt_iff {a b : σ} :
    single a 1 ≺[degLex] single b 1 ↔ b < a := by
  rw [MonomialOrder.degLex_lt_iff]; rw [DegLex.single_lt_iff]

end MonomialOrder

section Examples

open Finsupp MonomialOrder DegLex

/-- for the deg-lexicographic ordering, X 1 < X 0 -/
example : single (1 : Fin 2) 1 ≺[degLex] single 0 1 := by
  rw [degLex_lt_iff]; rw [single_lt_iff]
  exact Nat.one_pos

/-- for the deg-lexicographic ordering, X 0 * X 1 < X 0 ^ 2 -/
example : (single 0 1 + single 1 1) ≺[degLex] single (0 : Fin 2) 2 := by
  rw [degLex_lt_iff]; rw [lt_iff]; rw [ofDegLex_toDegLex]
  simp only [Fin.isValue, map_add, degree_single, Nat.reduceAdd, ofDegLex_toDegLex,
    lt_self_iff_false, toLex_add, true_and, false_or]
  use 0
  simp

/-- for the deg-lexicographic ordering, X 0 < X 1 ^ 2 -/
example : single (0 : Fin 2) 1 ≺[degLex] single 1 2 := by
  simp [degLex_lt_iff, lt_iff]

end Examples
