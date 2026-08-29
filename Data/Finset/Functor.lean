/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kim Morrison
-/
module

public import Batteries.Control.AlternativeMonad
public import Mathlib.Data.Finset.Lattice.Union
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Multiset.Functor

/-!
# Functoriality of `Finset`

This file defines the functor structure of `Finset`.

## TODO

Currently, all instances are classical because the functor classes want to run over all types. If
instead we could state that a functor is lawful/applicative/traversable... between two given types,
then we could provide the instances for types with decidable equality.
-/

@[expose] public section


universe u

open Function

namespace Finset

/-! ### Functor -/

section Functor

variable {α β : Type u} [forall P, Decidable P]

/--
Instance `functor` / 实例 `functor`

English:
instance functor
  signature: : Functor Finset where map f s
  body: s.image f

中文:
实例 functor
  签名: : 函子 有限集 where map f s
  定义体: s.image f
-/
protected instance functor : Functor Finset where map f s := s.image f

/--
Instance `lawfulFunctor` / 实例 `lawfulFunctor`

English:
instance lawfulFunctor
  signature: : LawfulFunctor Finset where
  body: image_id
  comp_map _ _ _ := image_image.symm
  map_const {α} {β} := by simp only [Functor.mapConst, Functor.map]

@[simp]

中文:
实例 lawfulFunctor
  签名: : Lawful函子 有限集 where
  定义体: image_id
  comp_map _ _ _ := image_image.symm
  map_const {α} {β} := by simp only [Functor.mapConst, Functor.map]

@[simp]

Depends on / 依赖: image_id
-/
instance lawfulFunctor : LawfulFunctor Finset where
  id_map _ := image_id
  comp_map _ _ _ := image_image.symm
  map_const {α} {β} := by simp only [Functor.mapConst, Functor.map]

@[simp]
/--
theorem `fmap_def` / 定理 `fmap_def`

English:
theorem fmap_def
  given: {s : Finset α} (f : α -> β)
  statement: f < > s = s.image f
  proof: rfl

中文:
定理 fmap_def
  条件: {s : 有限集 α} (f : α -> β)
  结论: f < > s = s.像 f
  证明: rfl
-/
theorem fmap_def {s : Finset α} (f : α -> β) : f < > s = s.image f := rfl

end Functor



/--
Instance `pure` / 实例 `pure`

English:
instance pure
  signature: : Pure Finset
  body: ⟨fun x => {x}⟩

@[simp]

中文:
实例 pure
  签名: : Pure 有限集
  定义体: ⟨fun x => {x}⟩

@[simp]
-/
protected instance pure : Pure Finset :=
  ⟨fun x => {x}⟩

@[simp]
/--
theorem `pure_def` / 定理 `pure_def`

English:
theorem pure_def
  given: {α}
  statement: (pure : α -> Finset α) = singleton
  proof: rfl

中文:
定理 pure_def
  条件: {α}
  结论: (pure : α -> 有限集 α) = singleton
  证明: rfl
-/
theorem pure_def {α} : (pure : α -> Finset α) = singleton := rfl

/-! ### Applicative functor -/


section Applicative

variable {α β : Type u} [forall P, Decidable P]

/--
Instance `applicative` / 实例 `applicative`

English:
instance applicative
  signature: : Applicative Finset
  body: { Finset.functor, Finset.pure with
    seq := fun t s => t.sup fun f => (s ()).image f
    seqLeft := fun s t => if t () = ∅ then ∅ else s
    seqRight := fun s t => if s = ∅ then ∅ else t () }

@[simp]

中文:
实例 applicative
  签名: : 适用 有限集
  定义体: { Finset.functor, Finset.pure with
    seq := fun t s => t.sup fun f => (s ()).image f
    seqLeft := fun s t => if t () = ∅ then ∅ else s
    seqRight := fun s t => if s = ∅ then ∅ else t () }

@[simp]
-/
protected instance applicative : Applicative Finset :=
  { Finset.functor, Finset.pure with
    seq := fun t s => t.sup fun f => (s ()).image f
    seqLeft := fun s t => if t () = ∅ then ∅ else s
    seqRight := fun s t => if s = ∅ then ∅ else t () }

@[simp]
/--
theorem `seq_def` / 定理 `seq_def`

English:
theorem seq_def
  given: (s : Finset α) (t : Finset (α -> β))
  statement: t <*> s = t.sup fun f => s.image f
  proof: rfl

@[simp]

中文:
定理 seq_def
  条件: (s : 有限集 α) (t : 有限集 (α -> β))
  结论: t <*> s = t.上确界 fun f => s.像 f
  证明: rfl

@[simp]
-/
theorem seq_def (s : Finset α) (t : Finset (α -> β)) : t <*> s = t.sup fun f => s.image f :=
  rfl

@[simp]
/--
theorem `seqLeft_def` / 定理 `seqLeft_def`

English:
theorem seqLeft_def
  given: (s : Finset α) (t : Finset β)
  statement: s <* t = if t = ∅ then ∅ else s
  proof: rfl

@[simp]

中文:
定理 seqLeft_def
  条件: (s : 有限集 α) (t : 有限集 β)
  结论: s <* t = if t = ∅ then ∅ else s
  证明: rfl

@[simp]
-/
theorem seqLeft_def (s : Finset α) (t : Finset β) : s <* t = if t = ∅ then ∅ else s :=
  rfl

@[simp]
/--
theorem `seqRight_def` / 定理 `seqRight_def`

English:
theorem seqRight_def
  given: (s : Finset α) (t : Finset β)
  statement: s *> t = if s = ∅ then ∅ else t
  proof: rfl

中文:
定理 seqRight_def
  条件: (s : 有限集 α) (t : 有限集 β)
  结论: s *> t = if s = ∅ then ∅ else t
  证明: rfl
-/
theorem seqRight_def (s : Finset α) (t : Finset β) : s *> t = if s = ∅ then ∅ else t :=
  rfl

/--
theorem `image₂_def` / 定理 `image₂_def`

English:
theorem image₂_def
  given: {α β γ : Type u} (f : α -> β -> γ) (s : Finset α) (t : Finset β)
  proof: by
  ext
  simp [mem_sup]

中文:
定理 image₂_def
  条件: {α β γ : 类型u} (f : α -> β -> γ) (s : 有限集 α) (t : 有限集 β)
  证明: by
  ext
  simp [mem_sup]

Depends on / 依赖: mem_sup
-/
theorem image₂_def {α β γ : Type u} (f : α -> β -> γ) (s : Finset α) (t : Finset β) :
image₂ f s t = f < > s <*> t := by
  ext
  simp [mem_sup]

/--
Instance `lawfulApplicative` / 实例 `lawfulApplicative`

English:
instance lawfulApplicative
  signature: : LawfulApplicative Finset
  body: { Finset.lawfulFunctor with
    seqLeft_eq := fun s t => by
      rw [seq_def]; rw [fmap_def]; rw [seqLeft_def]
      obtain rfl | ht := t.eq_empty_or_nonempty
      · simp_rw [image_empty, if_true]
        exact (sup_bot _).symm
      · ext a
        rw [if_neg ht.ne_empty]; rw [mem_sup]
        re

中文:
实例 lawfulApplicative
  签名: : 合法适用 有限集
  定义体: { Finset.lawfulFunctor with
    seqLeft_eq := fun s t => by
      rw [seq_def]; rw [fmap_def]; rw [seqLeft_def]
      obtain rfl | ht := t.eq_empty_or_nonempty
      · simp_rw [image_empty, if_true]
        exact (sup_bot _).symm
      · ext a
        rw [if_neg ht.ne_empty]; rw [mem_sup]
        re

Depends on / 依赖: Finset, Finset.lawfulFunctor, eq_empty_or_nonempty, fmap_def, ht.ne_empty, if_neg, if_true, image_empty, lawfulFunctor, mem_image, mem_image_const_self, mem_image_of_mem, mem_sup, ne_empty, seqLeft_def, seqLeft_eq, seqRight_eq, seq_def, simp_rw, sup_bot
-/
instance lawfulApplicative : LawfulApplicative Finset :=
  { Finset.lawfulFunctor with
    seqLeft_eq := fun s t => by
      rw [seq_def]; rw [fmap_def]; rw [seqLeft_def]
      obtain rfl | ht := t.eq_empty_or_nonempty
      · simp_rw [image_empty, if_true]
        exact (sup_bot _).symm
      · ext a
        rw [if_neg ht.ne_empty]; rw [mem_sup]
        refine ⟨fun ha => ⟨const _ a, mem_image_of_mem _ ha, mem_image_const_self.2 ht⟩, ?_⟩
        rintro ⟨f, hf, ha⟩
        rw [mem_image] at hf ha
        obtain ⟨b, hb, rfl⟩ := hf
        obtain ⟨_, _, rfl⟩ := ha
        exact hb
    seqRight_eq := fun s t => by
      rw [seq_def]; rw [fmap_def]; rw [seqRight_def]
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [if_pos rfl, image_empty, sup_empty, bot_eq_empty]
      · ext a
        rw [if_neg hs.ne_empty]; rw [mem_sup]
        refine ⟨fun ha => ⟨id, mem_image_const_self.2 hs, by rwa [image_id]⟩, ?_⟩
        rintro ⟨f, hf, ha⟩
        rw [mem_image] at hf ha
        obtain ⟨b, hb, rfl⟩ := ha
        obtain ⟨_, _, rfl⟩ := hf
        exact hb
    pure_seq := fun f s => by simp only [pure_def, seq_def, sup_singleton, fmap_def]
    map_pure := fun _ _ => image_singleton _ _
    seq_pure := fun _ _ => sup_singleton_apply _ _
    seq_assoc := fun s t u => by
      ext a
      simp_rw [seq_def, fmap_def]
      simp only [mem_sup, mem_image]
      constructor
      · rintro ⟨g, hg, b, ⟨f, hf, a, ha, rfl⟩, rfl⟩
        exact ⟨g ∘ f, ⟨comp g, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
      · rintro ⟨c, ⟨_, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
        exact ⟨g, hg, f a, ⟨f, hf, a, ha, rfl⟩, rfl⟩ }

/--
Instance `commApplicative` / 实例 `commApplicative`

English:
instance commApplicative
  signature: : CommApplicative Finset
  body: { Finset.lawfulApplicative with
    commutative_prod := fun s t => by
      simp_rw [seq_def, fmap_def, sup_image, sup_eq_biUnion]
      change (s.biUnion fun a => t.image fun b => (a, b))
        = t.biUnion fun b => s.image fun a => (a, b)
      trans s ×ˢ t <;> [rw [product_eq_biUnion]; rw [produ

中文:
实例 commApplicative
  签名: : 交换适用 有限集
  定义体: { Finset.lawfulApplicative with
    commutative_prod := fun s t => by
      simp_rw [seq_def, fmap_def, sup_image, sup_eq_biUnion]
      change (s.biUnion fun a => t.image fun b => (a, b))
        = t.biUnion fun b => s.image fun a => (a, b)
      trans s ×ˢ t <;> [rw [product_eq_biUnion]; rw [produ

Depends on / 依赖: Finset, Finset.lawfulApplicative, biUnion, commutative_prod, fmap_def, lawfulApplicative, product_eq_biUnion, product_eq_biUnion_right, s.biUnion, s.image, seq_def, simp_rw, sup_eq_biUnion, sup_image, t.biUnion, t.image
-/
instance commApplicative : CommApplicative Finset :=
  { Finset.lawfulApplicative with
    commutative_prod := fun s t => by
      simp_rw [seq_def, fmap_def, sup_image, sup_eq_biUnion]
      change (s.biUnion fun a => t.image fun b => (a, b))
        = t.biUnion fun b => s.image fun a => (a, b)
      trans s ×ˢ t <;> [rw [product_eq_biUnion]; rw [product_eq_biUnion_right]] }

end Applicative

/-! ### Monad -/


section Monad

variable [forall P, Decidable P]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monad Finset
  body: { Finset.applicative with bind := sup }

@[simp]

中文:
实例 :
  签名: 单子 有限集
  定义体: { Finset.applicative with bind := sup }

@[simp]

Depends on / 依赖: Finset, Finset.applicative, applicative
-/
instance : Monad Finset :=
  { Finset.applicative with bind := sup }

@[simp]
/--
theorem `bind_def` / 定理 `bind_def`

English:
theorem bind_def
  given: {α β}
  statement: (· >>= ·) = sup (α := Finset α) (β := β)
  proof: rfl

中文:
定理 bind_def
  条件: {α β}
  结论: (· >>= ·) = 上确界 (α := 有限集 α) (β := β)
  证明: rfl

Depends on / 依赖: Finset
-/
theorem bind_def {α β} : (· >>= ·) = sup (α := Finset α) (β := β) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad Finset
  body: { Finset.lawfulApplicative with
    bind_pure_comp := fun _ _ => sup_singleton_apply _ _
    bind_map := fun _ _ => rfl
    pure_bind := fun _ _ => sup_singleton
    bind_assoc := fun s f g => by simp only [bind, sup_eq_biUnion, biUnion_biUnion] }

中文:
实例 :
  签名: 合法单子 有限集
  定义体: { Finset.lawfulApplicative with
    bind_pure_comp := fun _ _ => sup_singleton_apply _ _
    bind_map := fun _ _ => rfl
    pure_bind := fun _ _ => sup_singleton
    bind_assoc := fun s f g => by simp only [bind, sup_eq_biUnion, biUnion_biUnion] }

Depends on / 依赖: Finset, Finset.lawfulApplicative, biUnion_biUnion, bind_assoc, bind_map, bind_pure_comp, lawfulApplicative, pure_bind, sup_eq_biUnion, sup_singleton, sup_singleton_apply
-/
instance : LawfulMonad Finset :=
  { Finset.lawfulApplicative with
    bind_pure_comp := fun _ _ => sup_singleton_apply _ _
    bind_map := fun _ _ => rfl
    pure_bind := fun _ _ => sup_singleton
    bind_assoc := fun s f g => by simp only [bind, sup_eq_biUnion, biUnion_biUnion] }

end Monad

/-! ### Alternative functor -/


section Alternative

variable [forall P, Decidable P]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AlternativeMonad Finset
  body: s union t ()
  failure := ∅

中文:
实例 :
  签名: AlternativeMonad 有限集
  定义体: s union t ()
  failure := ∅
-/
instance : AlternativeMonad Finset where
  orElse s t := s union t ()
  failure := ∅

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulAlternative Finset
  body: Finset.image_empty _
  failure_seq _ := Finset.sup_empty
  orElse_failure _ := Finset.union_empty _
  failure_orElse _ := Finset.empty_union _
.symm orElse_assoc _ _ _ := Finset.union_assoc _ _ _
  map_orElse _ _ _ := Finset.image_union _ _

中文:
实例 :
  签名: LawfulAlternative 有限集
  定义体: Finset.image_empty _
  failure_seq _ := Finset.sup_empty
  orElse_failure _ := Finset.union_empty _
  failure_orElse _ := Finset.empty_union _
.symm orElse_assoc _ _ _ := Finset.union_assoc _ _ _
  map_orElse _ _ _ := Finset.image_union _ _

Depends on / 依赖: Finset, Finset.image_empty, image_empty
-/
instance : LawfulAlternative Finset where
  map_failure _ := Finset.image_empty _
  failure_seq _ := Finset.sup_empty
  orElse_failure _ := Finset.union_empty _
  failure_orElse _ := Finset.empty_union _
.symm orElse_assoc _ _ _ := Finset.union_assoc _ _ _
  map_orElse _ _ _ := Finset.image_union _ _

end Alternative

/-! ### Traversable functor -/


section Traversable

variable {α β γ : Type u} {F G : Type u -> Type u} [Applicative F] [Applicative G]
  [CommApplicative F] [CommApplicative G]

/--
Definition of `traverse` / `traverse` 的定义

English:
definition traverse
  signature: [DecidableEq β] (f : α -> F β) (s : Finset α)
  body: Multiset.toFinset < > Multiset.traverse f s.1

@[simp]

中文:
定义 traverse
  签名: [DecidableEq β] (f : α -> F β) (s : 有限集 α)
  定义体: Multiset.toFinset < > Multiset.traverse f s.1

@[simp]

Depends on / 依赖: Multiset, Multiset.toFinset, Multiset.traverse, toFinset, traverse
-/
def traverse [DecidableEq β] (f : α -> F β) (s : Finset α) : F (Finset β) :=
Multiset.toFinset < > Multiset.traverse f s.1

@[simp]
/--
theorem `id_traverse` / 定理 `id_traverse`

English:
theorem id_traverse
  given: [DecidableEq α] (s : Finset α)
  statement: traverse (pure : α -> Id α) s = pure s
  proof: by
  rw [traverse]; rw [Multiset.id_traverse]
  exact s.val_toFinset

中文:
定理 id_traverse
  条件: [DecidableEq α] (s : 有限集 α)
  结论: traverse (pure : α -> Id α) s = pure s
  证明: by
  rw [traverse]; rw [Multiset.id_traverse]
  exact s.val_toFinset

Depends on / 依赖: Multiset, Multiset.id_traverse, id_traverse, s.val_toFinset, traverse, val_toFinset
-/
theorem id_traverse [DecidableEq α] (s : Finset α) : traverse (pure : α -> Id α) s = pure s := by
  rw [traverse]; rw [Multiset.id_traverse]
  exact s.val_toFinset

open scoped Classical in
@[simp]
/--
theorem `map_comp_coe` / 定理 `map_comp_coe`

English:
theorem map_comp_coe
  given: (h : α -> β)
  proof: funext fun _ => image_toFinset

中文:
定理 map_comp_coe
  条件: (h : α -> β)
  证明: funext fun _ => image_toFinset

Depends on / 依赖: image_toFinset
-/
theorem map_comp_coe (h : α -> β) :
    Functor.map h ∘ Multiset.toFinset = Multiset.toFinset ∘ Functor.map h :=
  funext fun _ => image_toFinset

open scoped Classical in
@[simp]
/--
theorem `map_comp_coe_apply` / 定理 `map_comp_coe_apply`

English:
theorem map_comp_coe_apply
  given: (h : α -> β) (s : Multiset α)
  proof: congrFun (map_comp_coe h) s

中文:
定理 map_comp_coe_apply
  条件: (h : α -> β) (s : Multiset α)
  证明: congrFun (map_comp_coe h) s

Depends on / 依赖: map_comp_coe
-/
theorem map_comp_coe_apply (h : α -> β) (s : Multiset α) :
    s.toFinset.image h = (h <$> s).toFinset :=
  congrFun (map_comp_coe h) s

open scoped Classical in
/--
theorem `map_traverse` / 定理 `map_traverse`

English:
theorem map_traverse
  given: (g : α -> G β) (h : β -> γ) (s : Finset α)
  proof: by
  unfold traverse
  simp only [Functor.map_map, fmap_def, map_comp_coe_apply, Multiset.fmap_def, ←
    Multiset.map_traverse]

中文:
定理 map_traverse
  条件: (g : α -> G β) (h : β -> γ) (s : 有限集 α)
  证明: by
  unfold traverse
  simp only [Functor.map_map, fmap_def, map_comp_coe_apply, Multiset.fmap_def, ←
    Multiset.map_traverse]

Depends on / 依赖: Functor, Functor.map_map, Multiset, Multiset.fmap_def, Multiset.map_traverse, fmap_def, map_comp_coe_apply, map_map, map_traverse, traverse
-/
theorem map_traverse (g : α -> G β) (h : β -> γ) (s : Finset α) :
Functor.map h < > traverse g s = traverse (Functor.map h ∘ g) s := by
  unfold traverse
  simp only [Functor.map_map, fmap_def, map_comp_coe_apply, Multiset.fmap_def, ←
    Multiset.map_traverse]

end Traversable

end Finset
