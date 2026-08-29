/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.EqToHom

/-!
# Functors from the category of the ordered set `ℕ`

In this file, we provide a constructor `Functor.ofSequence`
for functors `ℕ ⥤ C` which takes as an input a sequence
of morphisms `f : X n ⟶ X (n + 1)` for all `n : ℕ`.

We also provide a constructor `NatTrans.ofSequence` for natural
transformations between functors `ℕ ⥤ C` which allows to check
the naturality condition only for morphisms `n ⟶ n + 1`.

The duals of the above for functors `ℕᵒᵖ ⥤ C` are given by `Functor.ofOpSequence` and
`NatTrans.ofOpSequence`.

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C : Type*} [Category* C]

namespace Functor

variable {X : Nat -> C} (f : forall n, X n ⟶ X (n + 1))

namespace OfSequence

/--
lemma `congr_f` / 引理 `congr_f`

English:
lemma congr_f
  given: (i j : Nat) (h : i = j)
  proof: by
  subst h
  simp

中文:
引理 congr_f
  条件: (i j : 自然数) (h : i = j)
  证明: by
  subst h
  simp
-/
lemma congr_f (i j : Nat) (h : i = j) :
    f i = eqToHom (by rw [h]) ≫ f j ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : forall {X : Nat -> C} (_ : forall n, X n ⟶ X (n + 1)) (i j : Nat), i <= j -> (X i ⟶ X j)

中文:
定义 map
  签名: : 对任意 {X : 自然数 -> C} (_ : 对任意 n, X n ⟶ X (n + 1)) (i j : 自然数), i <= j -> (X i ⟶ X j)
-/
def map : forall {X : Nat -> C} (_ : forall n, X n ⟶ X (n + 1)) (i j : Nat), i <= j -> (X i ⟶ X j)
  | _, _, 0, 0 => fun _ => 𝟙 _
  | _, f, 0, 1 => fun _ => f 0
  | _, f, 0, l + 1 => fun _ => f 0 ≫ map (fun n => f (n + 1)) 0 l (by lia)
  | _, _, _ + 1, 0 => nofun
  | _, f, k + 1, l + 1 => fun _ => map (fun n => f (n + 1)) k l (by lia)

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (i : Nat)
  statement: map f i i (by lia) = 𝟙 _
  proof: by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi

中文:
引理 map_id
  条件: (i : 自然数)
  结论: map f i i (by lia) = 𝟙 _
  证明: by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi

Depends on / 依赖: intros, revert
-/
lemma map_id (i : Nat) : map f i i (by lia) = 𝟙 _ := by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi

/--
lemma `map_le_succ` / 引理 `map_le_succ`

English:
lemma map_le_succ
  given: (i : Nat)
  statement: map f i (i + 1) (by lia) = f i
  proof: by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi

@[reassoc]

中文:
引理 map_le_succ
  条件: (i : 自然数)
  结论: map f i (i + 1) (by lia) = f i
  证明: by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi

@[reassoc]

Depends on / 依赖: intros, revert
-/
lemma map_le_succ (i : Nat) : map f i (i + 1) (by lia) = f i := by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi

@[reassoc]
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (i j k : Nat) (hij : i <= j) (hjk : j <= k)
  proof: by
  induction i generalizing X j k with
  | zero =>
      induction j generalizing X k with
      | zero =>
          rw [map_id]; rw [id_comp]
      | succ j hj =>
          obtain (_ | _ | k) := k
          · lia
          · obtain rfl : j = 0 := by lia
            rw [map_id]; rw [comp_id]
          · simp only [map, Nat.reduceAdd]
            rw [hj (fun n => f (n + 1)) (k + 1) (by lia) (by lia)]
            obtain _ | j := j
            all_goals simp [map]
  | succ i hi =>
      rcases j, k with ⟨(_ | j), (_ | k)⟩
      · lia
      · lia
      · lia
      · exact hi _ j k (by lia) (by lia)

中文:
引理 map_comp
  条件: (i j k : 自然数) (hij : i <= j) (hjk : j <= k)
  证明: by
  induction i generalizing X j k with
  | zero =>
      induction j generalizing X k with
      | zero =>
          rw [map_id]; rw [id_comp]
      | succ j hj =>
          obtain (_ | _ | k) := k
          · lia
          · obtain rfl : j = 0 := by lia
            rw [map_id]; rw [comp_id]
          · simp only [map, Nat.reduceAdd]
            rw [hj (fun n => f (n + 1)) (k + 1) (by lia) (by lia)]
            obtain _ | j := j
            all_goals simp [map]
  | succ i hi =>
      rcases j, k with ⟨(_ | j), (_ | k)⟩
      · lia
      · lia
      · lia
      · exact hi _ j k (by lia) (by lia)

Depends on / 依赖: Nat.reduceAdd, all_goals, comp_id, generalizing, id_comp, map_id, reduceAdd
-/
lemma map_comp (i j k : Nat) (hij : i <= j) (hjk : j <= k) :
    map f i k (hij.trans hjk) = map f i j hij ≫ map f j k hjk := by
  induction i generalizing X j k with
  | zero =>
      induction j generalizing X k with
      | zero =>
          rw [map_id]; rw [id_comp]
      | succ j hj =>
          obtain (_ | _ | k) := k
          · lia
          · obtain rfl : j = 0 := by lia
            rw [map_id]; rw [comp_id]
          · simp only [map, Nat.reduceAdd]
            rw [hj (fun n => f (n + 1)) (k + 1) (by lia) (by lia)]
            obtain _ | j := j
            all_goals simp [map]
  | succ i hi =>
      rcases j, k with ⟨(_ | j), (_ | k)⟩
      · lia
      · lia
      · lia
      · exact hi _ j k (by lia) (by lia)

-- `map` has good definitional properties when applied to explicit natural numbers
example : map f 5 5 (by lia) = 𝟙 _ := rfl
example : map f 0 3 (by lia) = f 0 ≫ f 1 ≫ f 2 := rfl
example : map f 3 7 (by lia) = f 3 ≫ f 4 ≫ f 5 ≫ f 6 := rfl

end OfSequence

/-- The functor `ℕ ⥤ C` constructed from a sequence of
morphisms `f : X n ⟶ X (n + 1)` for all `n : ℕ`. -/
@[simps obj]
/--
Definition of `ofSequence` / `ofSequence` 的定义

English:
definition ofSequence
  signature: : Nat ⥤ C where
  body: X
  map {i j} φ := OfSequence.map f i j (leOfHom φ)
  map_id i := OfSequence.map_id f i
  map_comp {i j k} α β := OfSequence.map_comp f i j k (leOfHom α) (leOfHom β)

@[simp]

中文:
定义 ofSequence
  签名: : 自然数 ⥤ C where
  定义体: X
  map {i j} φ := OfSequence.map f i j (leOfHom φ)
  map_id i := OfSequence.map_id f i
  map_comp {i j k} α β := OfSequence.map_comp f i j k (leOfHom α) (leOfHom β)

@[simp]
-/
def ofSequence : Nat ⥤ C where
  obj := X
  map {i j} φ := OfSequence.map f i j (leOfHom φ)
  map_id i := OfSequence.map_id f i
  map_comp {i j k} α β := OfSequence.map_comp f i j k (leOfHom α) (leOfHom β)

@[simp]
/--
lemma `ofSequence_map_homOfLE_succ` / 引理 `ofSequence_map_homOfLE_succ`

English:
lemma ofSequence_map_homOfLE_succ
  given: (n : Nat)
  proof: OfSequence.map_le_succ f n

中文:
引理 ofSequence_map_homOfLE_succ
  条件: (n : 自然数)
  证明: OfSequence.map_le_succ f n

Depends on / 依赖: OfSequence, OfSequence.map_le_succ, map_le_succ
-/
lemma ofSequence_map_homOfLE_succ (n : Nat) :
    (ofSequence f).map (homOfLE (Nat.le_add_right n 1)) = f n :=
  OfSequence.map_le_succ f n

end Functor

namespace NatTrans

variable {F G : Nat ⥤ C} (app : forall (n : Nat), F.obj n ⟶ G.obj n)
  (naturality : forall (n : Nat), F.map (homOfLE (n.le_add_right 1)) ≫ app (n + 1) =
      app n ≫ G.map (homOfLE (n.le_add_right 1)))

/-- Constructor for natural transformations `F ⟶ G` in `ℕ ⥤ C` which takes as inputs
the morphisms `F.obj n ⟶ G.obj n` for all `n : ℕ` and the naturality condition only
for morphisms of the form `n ⟶ n + 1`. -/
@[simps app]
/--
Definition of `ofSequence` / `ofSequence` 的定义

English:
definition ofSequence
  signature: : F ⟶ G where
  body: app
  naturality := by
    intro i j φ
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (leOfHom φ)
    obtain rfl := Subsingleton.elim φ (homOfLE (by lia))
    revert i j
    induction k with
    | zero =>
        intro i j hk
        obtain rfl : j = i := by lia
        simp
    | succ k hk =>
        intro i j hk'
        obtain rfl : j = i + k + 1 := by lia
        simp only [← homOfLE_comp (show i <= i + k by lia) (show i + k <= i + k + 1 by lia),
          Functor.map_comp, assoc, naturality, reassoc_of% (hk rfl)]

中文:
定义 ofSequence
  签名: : F ⟶ G where
  定义体: app
  naturality := by
    intro i j φ
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (leOfHom φ)
    obtain rfl := Subsingleton.elim φ (homOfLE (by lia))
    revert i j
    induction k with
    | zero =>
        intro i j hk
        obtain rfl : j = i := by lia
        simp
    | succ k hk =>
        intro i j hk'
        obtain rfl : j = i + k + 1 := by lia
        simp only [← homOfLE_comp (show i <= i + k by lia) (show i + k <= i + k + 1 by lia),
          Functor.map_comp, assoc, naturality, reassoc_of% (hk rfl)]
-/
def ofSequence : F ⟶ G where
  app := app
  naturality := by
    intro i j φ
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (leOfHom φ)
    obtain rfl := Subsingleton.elim φ (homOfLE (by lia))
    revert i j
    induction k with
    | zero =>
        intro i j hk
        obtain rfl : j = i := by lia
        simp
    | succ k hk =>
        intro i j hk'
        obtain rfl : j = i + k + 1 := by lia
        simp only [← homOfLE_comp (show i <= i + k by lia) (show i + k <= i + k + 1 by lia),
          Functor.map_comp, assoc, naturality, reassoc_of% (hk rfl)]

end NatTrans

namespace Functor

variable {X : Nat -> C} (f : forall n, X (n + 1) ⟶ X n)

/-- The functor `ℕᵒᵖ ⥤ C` constructed from a sequence of
morphisms `f : X (n + 1) ⟶ X n` for all `n : ℕ`. -/
@[simps! obj]
/--
Definition of `ofOpSequence` / `ofOpSequence` 的定义

English:
definition ofOpSequence
  signature: : Natᵒᵖ ⥤ C
  body: (ofSequence (fun n => (f n).op)).leftOp

中文:
定义 ofOpSequence
  签名: : 自然数ᵒᵖ ⥤ C
  定义体: (ofSequence (fun n => (f n).op)).leftOp

Depends on / 依赖: leftOp, ofSequence
-/
def ofOpSequence : Natᵒᵖ ⥤ C := (ofSequence (fun n => (f n).op)).leftOp

-- `ofOpSequence` has good definitional properties when applied to explicit natural numbers
example : (ofOpSequence f).map (homOfLE (show 5 <= 5 by lia)).op = 𝟙 _ := rfl
example : (ofOpSequence f).map (homOfLE (show 0 <= 3 by lia)).op = (f 2 ≫ f 1) ≫ f 0 := rfl
example : (ofOpSequence f).map (homOfLE (show 3 <= 7 by lia)).op =
    ((f 6 ≫ f 5) ≫ f 4) ≫ f 3 := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `ofOpSequence_map_homOfLE_succ` / 引理 `ofOpSequence_map_homOfLE_succ`

English:
lemma ofOpSequence_map_homOfLE_succ
  given: (n : Nat)
  proof: by
  simp [ofOpSequence]

中文:
引理 ofOpSequence_map_homOfLE_succ
  条件: (n : 自然数)
  证明: by
  simp [ofOpSequence]

Depends on / 依赖: ofOpSequence
-/
lemma ofOpSequence_map_homOfLE_succ (n : Nat) :
    (ofOpSequence f).map (homOfLE (Nat.le_add_right n 1)).op = f n := by
  simp [ofOpSequence]

end Functor

namespace NatTrans

variable {F G : Natᵒᵖ ⥤ C} (app : forall (n : Nat), F.obj ⟨n⟩ ⟶ G.obj ⟨n⟩)
  (naturality : forall (n : Nat), F.map (homOfLE (n.le_add_right 1)).op ≫ app n =
      app (n + 1) ≫ G.map (homOfLE (n.le_add_right 1)).op)

/-- Constructor for natural transformations `F ⟶ G` in `ℕᵒᵖ ⥤ C` which takes as inputs
the morphisms `F.obj ⟨n⟩ ⟶ G.obj ⟨n⟩` for all `n : ℕ` and the naturality condition only
for morphisms of the form `n ⟶ n + 1`. -/
@[simps!]
/--
Definition of `ofOpSequence` / `ofOpSequence` 的定义

English:
definition ofOpSequence
  signature: : F ⟶ G where
  body: app n.unop
  naturality _ _ f := by
    let φ : G.rightOp ⟶ F.rightOp := ofSequence (fun n => (app n).op)
      (fun n => Quiver.Hom.unop_inj (naturality n).symm)
    exact Quiver.Hom.op_inj (φ.naturality f.unop).symm

中文:
定义 ofOpSequence
  签名: : F ⟶ G where
  定义体: app n.unop
  naturality _ _ f := by
    let φ : G.rightOp ⟶ F.rightOp := ofSequence (fun n => (app n).op)
      (fun n => Quiver.Hom.unop_inj (naturality n).symm)
    exact Quiver.Hom.op_inj (φ.naturality f.unop).symm

Depends on / 依赖: n.unop
-/
def ofOpSequence : F ⟶ G where
  app n := app n.unop
  naturality _ _ f := by
    let φ : G.rightOp ⟶ F.rightOp := ofSequence (fun n => (app n).op)
      (fun n => Quiver.Hom.unop_inj (naturality n).symm)
    exact Quiver.Hom.op_inj (φ.naturality f.unop).symm

end NatTrans

end CategoryTheory
