/-
Copyright (c) 2016 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Batteries.Control.AlternativeMonad
public import Mathlib.Control.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Notation

/-!
# Functoriality of `Set`

This file defines the functor structure of `Set`.
-/

@[expose] public section

universe u

open Function Set.Notation

namespace Set

variable {α β : Type u} {s : Set α} {f : α -> Set β}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Alternative Set
  body: {a}
  seq s t := s.seq (t ())
  seqLeft s t := {a | a in s ∧ (t ()).Nonempty}
  seqRight s t := {b | s.Nonempty ∧ b in t ()}
  map := Set.image
  orElse s t := s union t ()
  failure := ∅

@[simp]

中文:
实例 :
  签名: Alternative Set
  定义体: {a}
  seq s t := s.seq (t ())
  seqLeft s t := {a | a in s ∧ (t ()).Nonempty}
  seqRight s t := {b | s.Nonempty ∧ b in t ()}
  map := Set.image
  orElse s t := s union t ()
  failure := ∅

@[simp]
-/
instance : Alternative Set where
  pure a := {a}
  seq s t := s.seq (t ())
  seqLeft s t := {a | a in s ∧ (t ()).Nonempty}
  seqRight s t := {b | s.Nonempty ∧ b in t ()}
  map := Set.image
  orElse s t := s union t ()
  failure := ∅

@[simp]
/--
theorem `fmap_eq_image` / 定理 `fmap_eq_image`

English:
theorem fmap_eq_image
  given: (f : α -> β)
  statement: f < > s = f '' s
  proof: rfl

@[simp]

中文:
定理 fmap_eq_image
  条件: (f : α -> β)
  结论: f < > s = f '' s
  证明: rfl

@[simp]
-/
theorem fmap_eq_image (f : α -> β) : f < > s = f '' s :=
  rfl

@[simp]
/--
theorem `seq_eq_set_seq` / 定理 `seq_eq_set_seq`

English:
theorem seq_eq_set_seq
  given: (s : Set (α -> β)) (t : Set α)
  statement: s <*> t = s.seq t
  proof: rfl

@[simp]

中文:
定理 seq_eq_set_seq
  条件: (s : Set (α -> β)) (t : Set α)
  结论: s <*> t = s.seq t
  证明: rfl

@[simp]
-/
theorem seq_eq_set_seq (s : Set (α -> β)) (t : Set α) : s <*> t = s.seq t :=
  rfl

@[simp]
/--
theorem `seqLeft_def` / 定理 `seqLeft_def`

English:
theorem seqLeft_def
  given: (s : Set α) (t : Set β)
  statement: s <* t = {a | a in s ∧ t.Nonempty}
  proof: rfl

@[simp]

中文:
定理 seqLeft_def
  条件: (s : Set α) (t : Set β)
  结论: s <* t = {a | a in s ∧ t.Nonempty}
  证明: rfl

@[simp]
-/
theorem seqLeft_def (s : Set α) (t : Set β) : s <* t = {a | a in s ∧ t.Nonempty} :=
  rfl

@[simp]
/--
theorem `seqRight_def` / 定理 `seqRight_def`

English:
theorem seqRight_def
  given: (s : Set α) (t : Set β)
  statement: s *> t = {a | s.Nonempty ∧ a in t}
  proof: rfl

@[simp]

中文:
定理 seqRight_def
  条件: (s : Set α) (t : Set β)
  结论: s *> t = {a | s.Nonempty ∧ a in t}
  证明: rfl

@[simp]
-/
theorem seqRight_def (s : Set α) (t : Set β) : s *> t = {a | s.Nonempty ∧ a in t} :=
  rfl

@[simp]
/--
theorem `pure_def` / 定理 `pure_def`

English:
theorem pure_def
  given: (a : α)
  statement: (pure a : Set α) = {a}
  proof: rfl

@[simp]

中文:
定理 pure_def
  条件: (a : α)
  结论: (pure a : Set α) = {a}
  证明: rfl

@[simp]
-/
theorem pure_def (a : α) : (pure a : Set α) = {a} :=
  rfl

@[simp]
/--
theorem `failure_def` / 定理 `failure_def`

English:
theorem failure_def
  statement: (failure : Set α) = ∅
  proof: rfl

@[simp]

中文:
定理 failure_def
  结论: (failure : Set α) = ∅
  证明: rfl

@[simp]
-/
theorem failure_def : (failure : Set α) = ∅ :=
  rfl

@[simp]
/--
theorem `orElse_def` / 定理 `orElse_def`

English:
theorem orElse_def
  given: (s : Set α) (t : Set α)
  statement: (s <|> t) = s union t
  proof: rfl

中文:
定理 orElse_def
  条件: (s : Set α) (t : Set α)
  结论: (s <|> t) = s union t
  证明: rfl
-/
theorem orElse_def (s : Set α) (t : Set α) : (s <|> t) = s union t :=
  rfl

/--
theorem `image2_def` / 定理 `image2_def`

English:
theorem image2_def
  given: {α β γ : Type u} (f : α -> β -> γ) (s : Set α) (t : Set β)
  proof: by
  ext
  simp

中文:
定理 image2_def
  条件: {α β γ : 类型u} (f : α -> β -> γ) (s : Set α) (t : Set β)
  证明: by
  ext
  simp
-/
theorem image2_def {α β γ : Type u} (f : α -> β -> γ) (s : Set α) (t : Set β) :
image2 f s t = f < > s <*> t := by
  ext
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulAlternative Set
  body: Set.singleton_seq
  seqLeft_eq _ _ := by simp [Set.seq, Set.image2, Set.nonempty_def]
  seqRight_eq s t := by simp [Set.seq, Set.image2, Set.nonempty_def]
  map_pure _ _ := Set.image_singleton
  seq_pure _ _ := Set.seq_singleton
  seq_assoc _ _ _ := Set.seq_seq
  map_failure _ := Set.image_empty _
 

中文:
实例 :
  签名: LawfulAlternative Set
  定义体: Set.singleton_seq
  seqLeft_eq _ _ := by simp [Set.seq, Set.image2, Set.nonempty_def]
  seqRight_eq s t := by simp [Set.seq, Set.image2, Set.nonempty_def]
  map_pure _ _ := Set.image_singleton
  seq_pure _ _ := Set.seq_singleton
  seq_assoc _ _ _ := Set.seq_seq
  map_failure _ := Set.image_empty _
 

Depends on / 依赖: Set.singleton_seq, singleton_seq
-/
instance : LawfulAlternative Set where
  pure_seq _ _ := Set.singleton_seq
  seqLeft_eq _ _ := by simp [Set.seq, Set.image2, Set.nonempty_def]
  seqRight_eq s t := by simp [Set.seq, Set.image2, Set.nonempty_def]
  map_pure _ _ := Set.image_singleton
  seq_pure _ _ := Set.seq_singleton
  seq_assoc _ _ _ := Set.seq_seq
  map_failure _ := Set.image_empty _
  failure_seq _ := Set.image2_empty_left
  orElse_failure _ := Set.union_empty _
  failure_orElse _ := Set.empty_union _
.symm orElse_assoc _ _ _ := Set.union_assoc _ _ _
  map_orElse _ _ _ := Set.image_union _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommApplicative Set
  body: prod_image_seq_comm

中文:
实例 :
  签名: CommApplicative Set
  定义体: prod_image_seq_comm

Depends on / 依赖: prod_image_seq_comm
-/
instance : CommApplicative Set where
  commutative_prod := prod_image_seq_comm

/-- The `Set` functor is a monad.

This is not a global instance because it does not have computational content,
so it does not make much sense using `do` notation in general.

Moreover, this would cause monad-related coercions and monad lifting logic to become activated.
Either use `attribute [local instance] Set.monad` to make it be a local instance
or use `SetM.run do ...` when `do` notation is wanted. -/
@[instance_reducible]
/--
Definition of `monad` / `monad` 的定义

English:
definition monad
  signature: : AlternativeMonad.{u} Set where
  body: inferInstance
  bind s f := ⋃ i in s, f i

中文:
定义 monad
  签名: : AlternativeMonad.{u} Set where
  定义体: inferInstance
  bind s f := ⋃ i in s, f i
-/
protected def monad : AlternativeMonad.{u} Set where
  __ : Alternative Set := inferInstance
  bind s f := ⋃ i in s, f i

section with_instance
attribute [local instance] Set.monad

@[simp]
/--
theorem `bind_def` / 定理 `bind_def`

English:
theorem bind_def
  statement: s >>= f = ⋃ i in s, f i
  proof: rfl

中文:
定理 bind_def
  结论: s >>= f = ⋃ i in s, f i
  证明: rfl
-/
theorem bind_def : s >>= f = ⋃ i in s, f i :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad Set
  body: (image_eq_iUnion _ _).symm
  bind_map _ _ := seq_def.symm
  pure_bind := biUnion_singleton
  bind_assoc _ _ _ := by simp only [bind_def, biUnion_iUnion]

中文:
实例 :
  签名: LawfulMonad Set
  定义体: (image_eq_iUnion _ _).symm
  bind_map _ _ := seq_def.symm
  pure_bind := biUnion_singleton
  bind_assoc _ _ _ := by simp only [bind_def, biUnion_iUnion]

Depends on / 依赖: image_eq_iUnion
-/
instance : LawfulMonad Set where
  bind_pure_comp _ _ := (image_eq_iUnion _ _).symm
  bind_map _ _ := seq_def.symm
  pure_bind := biUnion_singleton
  bind_assoc _ _ _ := by simp only [bind_def, biUnion_iUnion]

/-! ### Monadic coercion lemmas -/

variable {β : Set α} {γ : Set β}

/--
theorem `mem_coe_of_mem` / 定理 `mem_coe_of_mem`

English:
theorem mem_coe_of_mem
  given: {a : α} (ha : a in β) (ha' : ⟨a, ha⟩ in γ)
  statement: a in (γ : Set α)
  proof: ⟨_, ⟨⟨_, rfl⟩, _, ⟨ha', rfl⟩, rfl⟩⟩

中文:
定理 mem_coe_of_mem
  条件: {a : α} (ha : a in β) (ha' : ⟨a, ha⟩ in γ)
  结论: a in (γ : Set α)
  证明: ⟨_, ⟨⟨_, rfl⟩, _, ⟨ha', rfl⟩, rfl⟩⟩
-/
theorem mem_coe_of_mem {a : α} (ha : a in β) (ha' : ⟨a, ha⟩ in γ) : a in (γ : Set α) :=
  ⟨_, ⟨⟨_, rfl⟩, _, ⟨ha', rfl⟩, rfl⟩⟩

/--
theorem `coe_subset` / 定理 `coe_subset`

English:
theorem coe_subset
  statement: (γ : Set α) subseteq β
  proof: by
  intro _ ⟨_, ⟨⟨⟨_, ha⟩, rfl⟩, _, ⟨_, rfl⟩, _⟩⟩; convert! ha

中文:
定理 coe_subset
  结论: (γ : Set α) subseteq β
  证明: by
  intro _ ⟨_, ⟨⟨⟨_, ha⟩, rfl⟩, _, ⟨_, rfl⟩, _⟩⟩; convert! ha

Depends on / 依赖: convert
-/
theorem coe_subset : (γ : Set α) subseteq β := by
  intro _ ⟨_, ⟨⟨⟨_, ha⟩, rfl⟩, _, ⟨_, rfl⟩, _⟩⟩; convert! ha

/--
theorem `mem_of_mem_coe` / 定理 `mem_of_mem_coe`

English:
theorem mem_of_mem_coe
  given: {a : α} (ha : a in (γ : Set α))
  statement: ⟨a, coe_subset ha⟩ in γ
  proof: by
  rcases ha with ⟨_, ⟨_, rfl⟩, _, ⟨ha, rfl⟩, _⟩; convert! ha

中文:
定理 mem_of_mem_coe
  条件: {a : α} (ha : a in (γ : Set α))
  结论: ⟨a, coe_subset ha⟩ in γ
  证明: by
  rcases ha with ⟨_, ⟨_, rfl⟩, _, ⟨ha, rfl⟩, _⟩; convert! ha

Depends on / 依赖: convert
-/
theorem mem_of_mem_coe {a : α} (ha : a in (γ : Set α)) : ⟨a, coe_subset ha⟩ in γ := by
  rcases ha with ⟨_, ⟨_, rfl⟩, _, ⟨ha, rfl⟩, _⟩; convert! ha

/--
theorem `eq_univ_of_coe_eq` / 定理 `eq_univ_of_coe_eq`

English:
theorem eq_univ_of_coe_eq
  given: (hγ : (γ : Set α) = β)
  statement: γ = univ
  proof: eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_coe hγ.symm ▸ ha

中文:
定理 eq_univ_of_coe_eq
  条件: (hγ : (γ : Set α) = β)
  结论: γ = univ
  证明: eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_coe hγ.symm ▸ ha

Depends on / 依赖: eq_univ_of_forall, mem_of_mem_coe
-/
theorem eq_univ_of_coe_eq (hγ : (γ : Set α) = β) : γ = univ :=
eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_coe hγ.symm ▸ ha

/--
theorem `image_coe_eq_domRestrict_image` / 定理 `image_coe_eq_domRestrict_image`

English:
theorem image_coe_eq_domRestrict_image
  given: {δ : Type*} {f : α -> δ}
  statement: f '' γ = β.domRestrict f '' γ
  proof: ext fun _ =>
    ⟨fun ⟨_, h, ha⟩ => ⟨_, mem_of_mem_coe h, ha⟩, fun ⟨_, h, ha⟩ => ⟨_, mem_coe_of_mem _ h, ha⟩⟩

@[deprecated (since := "2026-07-19")]
alias image_coe_eq_restrict_image := image_coe_eq_domRestrict_image

中文:
定理 image_coe_eq_domRestrict_image
  条件: {δ : 类型} {f : α -> δ}
  结论: f '' γ = β.domRestrict f '' γ
  证明: ext fun _ =>
    ⟨fun ⟨_, h, ha⟩ => ⟨_, mem_of_mem_coe h, ha⟩, fun ⟨_, h, ha⟩ => ⟨_, mem_coe_of_mem _ h, ha⟩⟩

@[deprecated (since := "2026-07-19")]
alias image_coe_eq_restrict_image := image_coe_eq_domRestrict_image

Depends on / 依赖: mem_coe_of_mem, mem_of_mem_coe
-/
theorem image_coe_eq_domRestrict_image {δ : Type*} {f : α -> δ} : f '' γ = β.domRestrict f '' γ :=
  ext fun _ =>
    ⟨fun ⟨_, h, ha⟩ => ⟨_, mem_of_mem_coe h, ha⟩, fun ⟨_, h, ha⟩ => ⟨_, mem_coe_of_mem _ h, ha⟩⟩

@[deprecated (since := "2026-07-19")]
alias image_coe_eq_restrict_image := image_coe_eq_domRestrict_image

end with_instance

/-! ### Coercion applying functoriality for `Subtype.val`
The `Monad` instance gives a coercion using the internal function `Lean.Internal.coeM`.
In practice this is only used for applying the `Set` functor to `Subtype.val`,
as was defined in `Data.Set.Notation`. -/

attribute [local instance] Set.monad in
/--
theorem `coe_eq_image_val` / 定理 `coe_eq_image_val`

English:
theorem coe_eq_image_val
  given: (t : Set s)
  proof: by
  change ⋃ (x in t), {x.1} = _
  ext
  simp

中文:
定理 coe_eq_image_val
  条件: (t : Set s)
  证明: by
  change ⋃ (x in t), {x.1} = _
  ext
  simp
-/
theorem coe_eq_image_val (t : Set s) :
    @Lean.Internal.coeM Set s α _ _ t = Subtype.val '' t := by
  change ⋃ (x in t), {x.1} = _
  ext
  simp

variable {β : Set α} {γ : Set β} {a : α}

/--
theorem `mem_image_val_of_mem` / 定理 `mem_image_val_of_mem`

English:
theorem mem_image_val_of_mem
  given: (ha : a in β) (ha' : ⟨a, ha⟩ in γ)
  statement: a in (γ : Set α)
  proof: ⟨_, ha', rfl⟩

中文:
定理 mem_image_val_of_mem
  条件: (ha : a in β) (ha' : ⟨a, ha⟩ in γ)
  结论: a in (γ : Set α)
  证明: ⟨_, ha', rfl⟩
-/
theorem mem_image_val_of_mem (ha : a in β) (ha' : ⟨a, ha⟩ in γ) : a in (γ : Set α) :=
  ⟨_, ha', rfl⟩

/--
theorem `image_val_subset` / 定理 `image_val_subset`

English:
theorem image_val_subset
  statement: (γ : Set α) subseteq β
  proof: Subtype.coe_image_subset _ _

中文:
定理 image_val_subset
  结论: (γ : Set α) subseteq β
  证明: Subtype.coe_image_subset _ _

Depends on / 依赖: Subtype, Subtype.coe_image_subset, coe_image_subset
-/
theorem image_val_subset : (γ : Set α) subseteq β := Subtype.coe_image_subset _ _

/--
theorem `mem_of_mem_image_val` / 定理 `mem_of_mem_image_val`

English:
theorem mem_of_mem_image_val
  given: (ha : a in (γ : Set α))
  statement: ⟨a, image_val_subset ha⟩ in γ
  proof: by
  rcases ha with ⟨_, ha, rfl⟩; exact ha

中文:
定理 mem_of_mem_image_val
  条件: (ha : a in (γ : Set α))
  结论: ⟨a, image_val_subset ha⟩ in γ
  证明: by
  rcases ha with ⟨_, ha, rfl⟩; exact ha
-/
theorem mem_of_mem_image_val (ha : a in (γ : Set α)) : ⟨a, image_val_subset ha⟩ in γ := by
  rcases ha with ⟨_, ha, rfl⟩; exact ha

/--
theorem `eq_univ_of_image_val_eq` / 定理 `eq_univ_of_image_val_eq`

English:
theorem eq_univ_of_image_val_eq
  given: (hγ : (γ : Set α) = β)
  statement: γ = univ
  proof: eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_image_val hγ.symm ▸ ha

中文:
定理 eq_univ_of_image_val_eq
  条件: (hγ : (γ : Set α) = β)
  结论: γ = univ
  证明: eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_image_val hγ.symm ▸ ha

Depends on / 依赖: eq_univ_of_forall, mem_of_mem_image_val
-/
theorem eq_univ_of_image_val_eq (hγ : (γ : Set α) = β) : γ = univ :=
eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_image_val hγ.symm ▸ ha

/--
theorem `image_image_val_eq_domRestrict_image` / 定理 `image_image_val_eq_domRestrict_image`

English:
theorem image_image_val_eq_domRestrict_image
  given: {δ : Type*} {f : α -> δ}
  proof: by
  ext; simp

@[deprecated (since := "2026-07-19")]
alias image_image_val_eq_restrict_image := image_image_val_eq_domRestrict_image

中文:
定理 image_image_val_eq_domRestrict_image
  条件: {δ : 类型} {f : α -> δ}
  证明: by
  ext; simp

@[deprecated (since := "2026-07-19")]
alias image_image_val_eq_restrict_image := image_image_val_eq_domRestrict_image
-/
theorem image_image_val_eq_domRestrict_image {δ : Type*} {f : α -> δ} :
    f '' γ = β.domRestrict f '' γ := by
  ext; simp

@[deprecated (since := "2026-07-19")]
alias image_image_val_eq_restrict_image := image_image_val_eq_domRestrict_image

end Set

/-! ### Wrapper to enable the `Set` monad -/

/--
Definition of `SetM` / `SetM` 的定义

English:
definition SetM
  signature: (α : Type u)
  body: Set α

中文:
定义 SetM
  签名: (α : 类型u)
  定义体: Set α
-/
def SetM (α : Type u) := Set α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AlternativeMonad SetM
  body: fast_instance% Set.monad

中文:
实例 :
  签名: AlternativeMonad SetM
  定义体: fast_instance% Set.monad

Depends on / 依赖: Set.monad, fast_instance
-/
instance : AlternativeMonad SetM := fast_instance% Set.monad

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad SetM
  body: Set.instLawfulMonad

中文:
实例 :
  签名: LawfulMonad SetM
  定义体: Set.instLawfulMonad

Depends on / 依赖: Set.instLawfulMonad, instLawfulMonad
-/
instance : LawfulMonad SetM := Set.instLawfulMonad

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulAlternative SetM
  body: Set.instLawfulAlternative

中文:
实例 :
  签名: LawfulAlternative SetM
  定义体: Set.instLawfulAlternative

Depends on / 依赖: Set.instLawfulAlternative, instLawfulAlternative
-/
instance : LawfulAlternative SetM := Set.instLawfulAlternative

/--
Definition of `SetM.run` / `SetM.run` 的定义

English:
definition SetM.run
  signature: {α : Type*} (s : SetM α)
  body: s

中文:
定义 SetM.run
  签名: {α : 类型} (s : SetM α)
  定义体: s
-/
protected def SetM.run {α : Type*} (s : SetM α) : Set α := s
