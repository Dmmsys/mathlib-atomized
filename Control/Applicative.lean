/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Control.Functor
public import Mathlib.Control.Basic

import Mathlib.Tactic.Attr.Register

/-!
# `applicative` instances

This file provides `Applicative` instances for concrete functors:
* `id`
* `Functor.comp`
* `Functor.const`
* `Functor.add_const`
-/

public section

universe u v w

section Lemmas

open Function

variable {F : Type u -> Type v}
variable [Applicative F] [LawfulApplicative F]
variable {α β γ σ : Type u}

/--
theorem `Applicative.map_seq_map` / 定理 `Applicative.map_seq_map`

English:
theorem Applicative.map_seq_map
  given: (f : α -> β -> γ) (g : σ -> β) (x : F α) (y : F σ)
  proof: by
  simp [functor_norm, Function.comp_def]

中文:
定理 适用.map_seq_map
  条件: (f : α -> β -> γ) (g : σ -> β) (x : F α) (y : F σ)
  证明: by
  simp [functor_norm, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, functor_norm
-/
theorem Applicative.map_seq_map (f : α -> β -> γ) (g : σ -> β) (x : F α) (y : F σ) :
f < > x <*> g < > y = ((· ∘ g) ∘ f) < > x <*> y := by
  simp [functor_norm, Function.comp_def]

/--
theorem `Applicative.pure_seq_eq_map'` / 定理 `Applicative.pure_seq_eq_map'`

English:
theorem Applicative.pure_seq_eq_map'
  given: (f : α -> β)
  statement: ((pure f : F (α -> β)) <*> ·) = (f <$> ·)
  proof: by
  simp [functor_norm]

中文:
定理 适用.pure_seq_eq_map'
  条件: (f : α -> β)
  结论: ((pure f : F (α -> β)) <*> ·) = (f <$> ·)
  证明: by
  simp [functor_norm]

Depends on / 依赖: functor_norm
-/
theorem Applicative.pure_seq_eq_map' (f : α -> β) : ((pure f : F (α -> β)) <*> ·) = (f <$> ·) := by
  simp [functor_norm]

set_option linter.overlappingInstances false in
/--
theorem `Applicative.ext` / 定理 `Applicative.ext`

English:
theorem Applicative.ext
  given: {F}
  proof: by
      funext α x
      apply H1
    obtain rfl : @s1 = @s2 := by
      funext α β f x
      exact H2 f (x Unit.unit)
    obtain ⟨seqLeft_eq1, seqRight_eq1, pure_seq1, -⟩ := L1
    obtain ⟨seqLeft_eq2, seqRight_eq2, pure_seq2, -⟩ := L2
    obtain rfl : F1 = F2 := by
      apply Functor.ext
      i

中文:
定理 适用.ext
  条件: {F}
  证明: by
      funext α x
      apply H1
    obtain rfl : @s1 = @s2 := by
      funext α β f x
      exact H2 f (x Unit.unit)
    obtain ⟨seqLeft_eq1, seqRight_eq1, pure_seq1, -⟩ := L1
    obtain ⟨seqLeft_eq2, seqRight_eq2, pure_seq2, -⟩ := L2
    obtain rfl : F1 = F2 := by
      apply Functor.ext
      i

Depends on / 依赖: seqLeft, seqRight
-/
theorem Applicative.ext {F} :
    forall {A1 : Applicative F} {A2 : Applicative F} [@LawfulApplicative F A1] [@LawfulApplicative F A2],
      (forall {α : Type u} (x : α), @Pure.pure _ A1.toPure _ x = @Pure.pure _ A2.toPure _ x) ->
      (forall {α β : Type u} (f : F (α -> β)) (x : F α),
          @Seq.seq _ A1.toSeq _ _ f (fun _ => x) = @Seq.seq _ A2.toSeq _ _ f (fun _ => x)) ->
      A1 = A2
  | { toFunctor := F1, seq := s1, pure := p1, seqLeft := sl1, seqRight := sr1 },
    { toFunctor := F2, seq := s2, pure := p2, seqLeft := sl2, seqRight := sr2 },
    L1, L2, H1, H2 => by
    obtain rfl : @p1 = @p2 := by
      funext α x
      apply H1
    obtain rfl : @s1 = @s2 := by
      funext α β f x
      exact H2 f (x Unit.unit)
    obtain ⟨seqLeft_eq1, seqRight_eq1, pure_seq1, -⟩ := L1
    obtain ⟨seqLeft_eq2, seqRight_eq2, pure_seq2, -⟩ := L2
    obtain rfl : F1 = F2 := by
      apply Functor.ext
      intros
      exact (pure_seq1 _ _).symm.trans (pure_seq2 _ _)
    congr <;> funext α β x y
    · exact (seqLeft_eq1 _ (y Unit.unit)).trans (seqLeft_eq2 _ _).symm
    · exact (seqRight_eq1 _ (y Unit.unit)).trans (seqRight_eq2 _ (y Unit.unit)).symm

end Lemmas

-- Porting note: we have a monad instance for `Id` but not `id`, mathport can't tell
-- which one is intended

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommApplicative Id
  body: rfl

中文:
实例 :
  签名: 交换适用 Id
  定义体: rfl
-/
instance : CommApplicative Id where commutative_prod _ _ := rfl

namespace Functor

namespace Comp

open Function hiding comp

open Functor

variable {F : Type u -> Type w} {G : Type v -> Type u}
variable [Applicative F] [Applicative G]
variable [LawfulApplicative F] [LawfulApplicative G]
variable {α β γ : Type v}

/--
theorem `map_pure` / 定理 `map_pure`

English:
theorem map_pure
  given: (f : α -> β) (x : α)
  statement: (f <$> pure x : Comp F G β) = pure (f x)
  proof: Comp.ext by simp

中文:
定理 map_pure
  条件: (f : α -> β) (x : α)
  结论: (f <$> pure x : 复合 F G β) = pure (f x)
  证明: Comp.ext by simp

Depends on / 依赖: Comp.ext
-/
theorem map_pure (f : α -> β) (x : α) : (f <$> pure x : Comp F G β) = pure (f x) :=
Comp.ext by simp

/--
theorem `seq_pure` / 定理 `seq_pure`

English:
theorem seq_pure
  given: (f : Comp F G (α -> β)) (x : α)
  statement: f <*> pure x = (fun g : α -> β => g x) < > f
  proof: Comp.ext by simp [functor_norm]

中文:
定理 seq_pure
  条件: (f : 复合 F G (α -> β)) (x : α)
  结论: f <*> pure x = (fun g : α -> β => g x) < > f
  证明: Comp.ext by simp [functor_norm]

Depends on / 依赖: Comp.ext, functor_norm
-/
theorem seq_pure (f : Comp F G (α -> β)) (x : α) : f <*> pure x = (fun g : α -> β => g x) < > f :=
Comp.ext by simp [functor_norm]

/--
theorem `seq_assoc` / 定理 `seq_assoc`

English:
theorem seq_assoc
  given: (x : Comp F G α) (f : Comp F G (α -> β)) (g : Comp F G (β -> γ))
  proof: Comp.ext by simp [comp_def, functor_norm]

中文:
定理 seq_assoc
  条件: (x : 复合 F G α) (f : 复合 F G (α -> β)) (g : 复合 F G (β -> γ))
  证明: Comp.ext by simp [comp_def, functor_norm]

Depends on / 依赖: Comp.ext, comp_def, functor_norm
-/
theorem seq_assoc (x : Comp F G α) (f : Comp F G (α -> β)) (g : Comp F G (β -> γ)) :
g <*> (f <*> x) = @Function.comp α β γ < > g <*> f <*> x :=
Comp.ext by simp [comp_def, functor_norm]

/--
theorem `pure_seq_eq_map` / 定理 `pure_seq_eq_map`

English:
theorem pure_seq_eq_map
  given: (f : α -> β) (x : Comp F G α)
  statement: pure f <*> x = f < > x
  proof: Comp.ext by simp [functor_norm]

中文:
定理 pure_seq_eq_map
  条件: (f : α -> β) (x : 复合 F G α)
  结论: pure f <*> x = f < > x
  证明: Comp.ext by simp [functor_norm]

Depends on / 依赖: Comp.ext, functor_norm
-/
theorem pure_seq_eq_map (f : α -> β) (x : Comp F G α) : pure f <*> x = f < > x :=
Comp.ext by simp [functor_norm]

-- TODO: the first two results were handled by `control_laws_tac` in mathlib3
/--
Instance `instLawfulApplicativeComp` / 实例 `instLawfulApplicativeComp`

English:
instance instLawfulApplicativeComp
  signature: : LawfulApplicative (Comp F G) where
  body: by intros; rfl
  seqRight_eq := by intros; rfl
  pure_seq := Comp.pure_seq_eq_map
  map_pure := Comp.map_pure
  seq_pure := Comp.seq_pure
  seq_assoc := Comp.seq_assoc

中文:
实例 instLawfulApplicativeComp
  签名: : 合法适用 (复合 F G) where
  定义体: by intros; rfl
  seqRight_eq := by intros; rfl
  pure_seq := Comp.pure_seq_eq_map
  map_pure := Comp.map_pure
  seq_pure := Comp.seq_pure
  seq_assoc := Comp.seq_assoc

Depends on / 依赖: Comp.map_pure, Comp.pure_seq_eq_map, Comp.seq_assoc, Comp.seq_pure, intros, map_pure, pure_seq, pure_seq_eq_map, seqRight_eq, seq_assoc, seq_pure
-/
instance instLawfulApplicativeComp : LawfulApplicative (Comp F G) where
  seqLeft_eq := by intros; rfl
  seqRight_eq := by intros; rfl
  pure_seq := Comp.pure_seq_eq_map
  map_pure := Comp.map_pure
  seq_pure := Comp.seq_pure
  seq_assoc := Comp.seq_assoc

/--
theorem `applicative_id_comp` / 定理 `applicative_id_comp`

English:
theorem applicative_id_comp
  given: {F} [AF : Applicative F] [LawfulApplicative F]
  proof: @Applicative.ext F _ _ (instLawfulApplicativeComp (F := Id)) _
    (fun _ => rfl) (fun _ _ => rfl)

中文:
定理 applicative_id_comp
  条件: {F} [AF : 适用 F] [合法适用 F]
  证明: @Applicative.ext F _ _ (instLawfulApplicativeComp (F := Id)) _
    (fun _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: Applicative, Applicative.ext, instLawfulApplicativeComp
-/
theorem applicative_id_comp {F} [AF : Applicative F] [LawfulApplicative F] :
    @instApplicativeComp Id F _ _ = AF :=
  @Applicative.ext F _ _ (instLawfulApplicativeComp (F := Id)) _
    (fun _ => rfl) (fun _ _ => rfl)

/--
theorem `applicative_comp_id` / 定理 `applicative_comp_id`

English:
theorem applicative_comp_id
  given: {F} [AF : Applicative F] [LawfulApplicative F]
  proof: @Applicative.ext F _ _ (instLawfulApplicativeComp (G := Id)) _
    (fun _ => rfl) (fun f x => show id <$> f <*> x = f <*> x by rw [id_map])

中文:
定理 applicative_comp_id
  条件: {F} [AF : 适用 F] [合法适用 F]
  证明: @Applicative.ext F _ _ (instLawfulApplicativeComp (G := Id)) _
    (fun _ => rfl) (fun f x => show id <$> f <*> x = f <*> x by rw [id_map])

Depends on / 依赖: Applicative, Applicative.ext, id_map, instLawfulApplicativeComp
-/
theorem applicative_comp_id {F} [AF : Applicative F] [LawfulApplicative F] :
    @Comp.instApplicativeComp F Id _ _ = AF :=
  @Applicative.ext F _ _ (instLawfulApplicativeComp (G := Id)) _
    (fun _ => rfl) (fun f x => show id <$> f <*> x = f <*> x by rw [id_map])

open CommApplicative

set_option backward.isDefEq.respectTransparency false in
instance {f : Type u -> Type w} {g : Type v -> Type u} [Applicative f] [Applicative g]
    [CommApplicative f] [CommApplicative g] : CommApplicative (Comp f g) where
  commutative_prod _ _ := by
    simp! [map, Seq.seq]
    rw [commutative_map]
    simp only [mk, flip, seq_map_assoc, Function.comp_def, map_map]
    congr
    funext x y
    rw [commutative_map]
    congr

end Comp

end Functor

open Functor

@[functor_norm]
/--
theorem `Comp.seq_mk` / 定理 `Comp.seq_mk`

English:
theorem Comp.seq_mk
  statement: {α β : Type w} {f : Type u -> Type v} {g : Type w -> Type u} [Applicative f]
  proof: rfl

中文:
定理 复合.seq_mk
  结论: {α β : 类型 w} {f : 类型u -> 类型v} {g : 类型 w -> 类型u} [适用 f]
  证明: rfl
-/
theorem Comp.seq_mk {α β : Type w} {f : Type u -> Type v} {g : Type w -> Type u} [Applicative f]
    [Applicative g] (h : f (g (α -> β))) (x : f (g α)) :
    Comp.mk h <*> Comp.mk x = Comp.mk ((· <*> ·) <$> h <*> x) :=
  rfl

-- Porting note: There is some awkwardness in the following definition now that we have `HMul`.

instance {α} [One α] [Mul α] : Applicative (Const α) where
  pure _ := (1 : α)
  seq f x := (show α from f) * (show α from x Unit.unit)

-- Porting note: `(· <*> ·)` needed to change to `Seq.seq` in the `simp`.
-- Also, `simp` didn't close `refl` goals.

set_option backward.isDefEq.respectTransparency false in
instance {α} [Monoid α] : LawfulApplicative (Const α) where
  map_pure _ _ := rfl
  seq_pure _ _ := by simp [Const.map, map, Seq.seq, pure, mul_one]
  pure_seq _ _ := by simp [Const.map, map, Seq.seq, pure, one_mul]
  seqLeft_eq _ _ := by simp [Seq.seq, SeqLeft.seqLeft]
  seqRight_eq _ _ := by simp [Seq.seq, SeqRight.seqRight]
  seq_assoc _ _ _ := by simp [Const.map, map, Seq.seq, mul_assoc]

instance {α} [Zero α] [Add α] : Applicative (AddConst α) where
  pure _ := (0 : α)
  seq f x := (show α from f) + (show α from x Unit.unit)

set_option backward.isDefEq.respectTransparency false in
instance {α} [AddMonoid α] : LawfulApplicative (AddConst α) where
  map_pure _ _ := rfl
  seq_pure _ _ := by simp [Const.map, map, Seq.seq, pure, add_zero]
  pure_seq _ _ := by simp [Const.map, map, Seq.seq, pure, zero_add]
  seqLeft_eq _ _ := by simp [Seq.seq, SeqLeft.seqLeft]
  seqRight_eq _ _ := by simp [Seq.seq, SeqRight.seqRight]
  seq_assoc _ _ _ := by simp [Const.map, map, Seq.seq, add_assoc]
