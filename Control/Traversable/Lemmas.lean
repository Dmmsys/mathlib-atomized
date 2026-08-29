/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Applicative
public import Mathlib.Control.Traversable.Basic

import Mathlib.Tactic.Attr.Register

/-!
# Traversing collections

This file proves basic properties of traversable and applicative functors and defines
`PureTransformation F`, the natural applicative transformation from the identity functor to `F`.

## References

Inspired by [The Essence of the Iterator Pattern][gibbons2009].
-/

@[expose] public section


universe u

open LawfulTraversable

open Function hiding comp

open Functor

attribute [functor_norm] LawfulTraversable.naturality

attribute [simp] LawfulTraversable.id_traverse

namespace Traversable

variable {t : Type u -> Type u}
variable [Traversable t] [LawfulTraversable t]
variable (F G : Type u -> Type u)
variable [Applicative F] [LawfulApplicative F]
variable [Applicative G] [LawfulApplicative G]
variable {α β γ : Type u}
variable (g : α -> F β)
variable (f : β -> γ)

/--
Definition of `PureTransformation` / `PureTransformation` 的定义

English:
definition PureTransformation
  signature: :
  body: @pure F _
  preserves_pure' _ := rfl
  preserves_seq' f x := by
    simp only [map_pure, seq_pure]
    rfl

@[simp]

中文:
定义 PureTransformation
  签名: :
  定义体: @pure F _
  preserves_pure' _ := rfl
  preserves_seq' f x := by
    simp only [map_pure, seq_pure]
    rfl

@[simp]
-/
def PureTransformation :
    ApplicativeTransformation Id F where
  app := @pure F _
  preserves_pure' _ := rfl
  preserves_seq' f x := by
    simp only [map_pure, seq_pure]
    rfl

@[simp]
/--
theorem `pureTransformation_apply` / 定理 `pureTransformation_apply`

English:
theorem pureTransformation_apply
  given: {α} (x : id α)
  statement: PureTransformation F x = pure x
  proof: rfl

中文:
定理 pureTransformation_apply
  条件: {α} (x : id α)
  结论: PureTransformation F x = pure x
  证明: rfl
-/
theorem pureTransformation_apply {α} (x : id α) : PureTransformation F x = pure x :=
  rfl

variable {F G}

/--
theorem `map_eq_traverse_id` / 定理 `map_eq_traverse_id`

English:
theorem map_eq_traverse_id
  statement: map (f := t) f = Id.run ∘ traverse (pure ∘ f)
  proof: funext fun y => (traverse_eq_map_id f y).symm

中文:
定理 map_eq_traverse_id
  结论: map (f := t) f = Id.run ∘ traverse (pure ∘ f)
  证明: funext fun y => (traverse_eq_map_id f y).symm

Depends on / 依赖: Id.run, traverse
-/
theorem map_eq_traverse_id : map (f := t) f = Id.run ∘ traverse (pure ∘ f) :=
  funext fun y => (traverse_eq_map_id f y).symm

/--
theorem `map_traverse` / 定理 `map_traverse`

English:
theorem map_traverse
  given: (x : t α)
  statement: map f < > traverse g x = traverse (map f ∘ g) x
  proof: by
  rw [map_eq_traverse_id f]
  refine (comp_traverse (pure ∘ f) g x).symm.trans ?_
  congr 1; apply Comp.applicative_comp_id

中文:
定理 map_traverse
  条件: (x : t α)
  结论: map f < > traverse g x = traverse (map f ∘ g) x
  证明: by
  rw [map_eq_traverse_id f]
  refine (comp_traverse (pure ∘ f) g x).symm.trans ?_
  congr 1; apply Comp.applicative_comp_id

Depends on / 依赖: Comp.applicative_comp_id, applicative_comp_id, comp_traverse, map_eq_traverse_id, symm.trans
-/
theorem map_traverse (x : t α) : map f < > traverse g x = traverse (map f ∘ g) x := by
  rw [map_eq_traverse_id f]
  refine (comp_traverse (pure ∘ f) g x).symm.trans ?_
  congr 1; apply Comp.applicative_comp_id

/--
theorem `traverse_map` / 定理 `traverse_map`

English:
theorem traverse_map
  given: (f : β -> F γ) (g : α -> β) (x : t α)
  proof: by
  rw [@map_eq_traverse_id t _ _ _ _ g]
  refine (comp_traverse (G := Id) f (pure ∘ g) x).symm.trans ?_
  congr 1; apply Comp.applicative_id_comp

中文:
定理 traverse_map
  条件: (f : β -> F γ) (g : α -> β) (x : t α)
  证明: by
  rw [@map_eq_traverse_id t _ _ _ _ g]
  refine (comp_traverse (G := Id) f (pure ∘ g) x).symm.trans ?_
  congr 1; apply Comp.applicative_id_comp

Depends on / 依赖: Comp.applicative_id_comp, applicative_id_comp, comp_traverse, map_eq_traverse_id, symm.trans
-/
theorem traverse_map (f : β -> F γ) (g : α -> β) (x : t α) :
    traverse f (g <$> x) = traverse (f ∘ g) x := by
  rw [@map_eq_traverse_id t _ _ _ _ g]
  refine (comp_traverse (G := Id) f (pure ∘ g) x).symm.trans ?_
  congr 1; apply Comp.applicative_id_comp

/--
theorem `pure_traverse` / 定理 `pure_traverse`

English:
theorem pure_traverse
  given: (x : t α)
  statement: traverse pure x = (pure x : F (t α))
  proof: by
  have : traverse pure x = pure (traverse (m := Id) pure x) :=
      (naturality (PureTransformation F) pure x).symm
  rwa [id_traverse] at this

中文:
定理 pure_traverse
  条件: (x : t α)
  结论: traverse pure x = (pure x : F (t α))
  证明: by
  have : traverse pure x = pure (traverse (m := Id) pure x) :=
      (naturality (PureTransformation F) pure x).symm
  rwa [id_traverse] at this

Depends on / 依赖: PureTransformation, id_traverse, naturality, traverse
-/
theorem pure_traverse (x : t α) : traverse pure x = (pure x : F (t α)) := by
  have : traverse pure x = pure (traverse (m := Id) pure x) :=
      (naturality (PureTransformation F) pure x).symm
  rwa [id_traverse] at this

/--
theorem `id_sequence` / 定理 `id_sequence`

English:
theorem id_sequence
  given: (x : t α)
  statement: sequence (f := Id) (pure <$> x) = pure x
  proof: by
  simp [sequence, traverse_map, id_traverse]

中文:
定理 id_sequence
  条件: (x : t α)
  结论: sequence (f := Id) (pure <$> x) = pure x
  证明: by
  simp [sequence, traverse_map, id_traverse]

Depends on / 依赖: id_traverse, sequence, traverse_map
-/
theorem id_sequence (x : t α) : sequence (f := Id) (pure <$> x) = pure x := by
  simp [sequence, traverse_map, id_traverse]

/--
theorem `comp_sequence` / 定理 `comp_sequence`

English:
theorem comp_sequence
  given: (x : t (F (G α)))
  proof: by
  simp only [sequence, traverse_map, id_comp]; rw [← comp_traverse]; simp [map_id]

中文:
定理 comp_sequence
  条件: (x : t (F (G α)))
  证明: by
  simp only [sequence, traverse_map, id_comp]; rw [← comp_traverse]; simp [map_id]

Depends on / 依赖: comp_traverse, id_comp, map_id, sequence, traverse_map
-/
theorem comp_sequence (x : t (F (G α))) :
    sequence (Comp.mk <$> x) = Comp.mk (sequence <$> sequence x) := by
  simp only [sequence, traverse_map, id_comp]; rw [← comp_traverse]; simp [map_id]

/--
theorem `naturality'` / 定理 `naturality'`

English:
theorem naturality'
  given: (η : ApplicativeTransformation F G) (x : t (F α))
  proof: by simp [sequence, naturality, traverse_map]

@[functor_norm]

中文:
定理 naturality'
  条件: (η : ApplicativeTransformation F G) (x : t (F α))
  证明: by simp [sequence, naturality, traverse_map]

@[functor_norm]

Depends on / 依赖: naturality, sequence, traverse_map
-/
theorem naturality' (η : ApplicativeTransformation F G) (x : t (F α)) :
    η (sequence x) = sequence (@η _ <$> x) := by simp [sequence, naturality, traverse_map]

@[functor_norm]
/--
theorem `traverse_id` / 定理 `traverse_id`

English:
theorem traverse_id
  statement: traverse pure = (pure : t α -> Id (t α))
  proof: by
  ext
  exact id_traverse _

@[functor_norm]

中文:
定理 traverse_id
  结论: traverse pure = (pure : t α -> Id (t α))
  证明: by
  ext
  exact id_traverse _

@[functor_norm]

Depends on / 依赖: id_traverse
-/
theorem traverse_id : traverse pure = (pure : t α -> Id (t α)) := by
  ext
  exact id_traverse _

@[functor_norm]
/--
theorem `traverse_comp` / 定理 `traverse_comp`

English:
theorem traverse_comp
  given: (g : α -> F β) (h : β -> G γ)
  proof: by
  ext
  exact comp_traverse _ _ _

中文:
定理 traverse_comp
  条件: (g : α -> F β) (h : β -> G γ)
  证明: by
  ext
  exact comp_traverse _ _ _

Depends on / 依赖: comp_traverse
-/
theorem traverse_comp (g : α -> F β) (h : β -> G γ) :
    traverse (Comp.mk ∘ map h ∘ g) =
      (Comp.mk ∘ map (traverse h) ∘ traverse g : t α -> Comp F G (t γ)) := by
  ext
  exact comp_traverse _ _ _

/--
theorem `traverse_eq_map_id'` / 定理 `traverse_eq_map_id'`

English:
theorem traverse_eq_map_id'
  given: (f : β -> γ)
  proof: by
  ext
  exact traverse_eq_map_id _ _

中文:
定理 traverse_eq_map_id'
  条件: (f : β -> γ)
  证明: by
  ext
  exact traverse_eq_map_id _ _

Depends on / 依赖: traverse_eq_map_id
-/
theorem traverse_eq_map_id' (f : β -> γ) :
    traverse (m := Id) (pure ∘ f) = pure ∘ (map f : t β -> t γ) := by
  ext
  exact traverse_eq_map_id _ _

-- @[functor_norm]
/--
theorem `traverse_map'` / 定理 `traverse_map'`

English:
theorem traverse_map'
  given: (g : α -> β) (h : β -> G γ)
  proof: by
  ext
  rw [comp_apply]; rw [traverse_map]

中文:
定理 traverse_map'
  条件: (g : α -> β) (h : β -> G γ)
  证明: by
  ext
  rw [comp_apply]; rw [traverse_map]

Depends on / 依赖: comp_apply, traverse_map
-/
theorem traverse_map' (g : α -> β) (h : β -> G γ) :
    traverse (h ∘ g) = (traverse h ∘ map g : t α -> G (t γ)) := by
  ext
  rw [comp_apply]; rw [traverse_map]

/--
theorem `map_traverse'` / 定理 `map_traverse'`

English:
theorem map_traverse'
  given: (g : α -> G β) (h : β -> γ)
  proof: by
  ext
  rw [comp_apply]; rw [map_traverse]

中文:
定理 map_traverse'
  条件: (g : α -> G β) (h : β -> γ)
  证明: by
  ext
  rw [comp_apply]; rw [map_traverse]

Depends on / 依赖: comp_apply, map_traverse
-/
theorem map_traverse' (g : α -> G β) (h : β -> γ) :
    traverse (map h ∘ g) = (map (map h) ∘ traverse g : t α -> G (t γ)) := by
  ext
  rw [comp_apply]; rw [map_traverse]

/--
theorem `naturality_pf` / 定理 `naturality_pf`

English:
theorem naturality_pf
  given: (η : ApplicativeTransformation F G) (f : α -> F β)
  proof: by
  ext
  rw [comp_apply]; rw [naturality]

中文:
定理 naturality_pf
  条件: (η : ApplicativeTransformation F G) (f : α -> F β)
  证明: by
  ext
  rw [comp_apply]; rw [naturality]

Depends on / 依赖: comp_apply, naturality
-/
theorem naturality_pf (η : ApplicativeTransformation F G) (f : α -> F β) :
    traverse (@η _ ∘ f) = @η _ ∘ (traverse f : t α -> F (t β)) := by
  ext
  rw [comp_apply]; rw [naturality]

end Traversable
