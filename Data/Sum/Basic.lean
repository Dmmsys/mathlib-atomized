/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Additional lemmas about sum types

Most of the former contents of this file have been moved to Batteries.
-/

@[expose] public section


universe u v w x

variable {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {γ δ : Type*}

/--
lemma `not_isLeft_and_isRight` / 引理 `not_isLeft_and_isRight`

English:
lemma not_isLeft_and_isRight
  given: {x : α oplus β}
  statement: ¬(x.isLeft ∧ x.isRight)
  proof: by simp

中文:
引理 not_isLeft_and_isRight
  条件: {x : α oplus β}
  结论: ¬(x.isLeft ∧ x.isRight)
  证明: by simp
-/
lemma not_isLeft_and_isRight {x : α oplus β} : ¬(x.isLeft ∧ x.isRight) := by simp

namespace Sum

@[simp]
/--
theorem `elim_swap` / 定理 `elim_swap`

English:
theorem elim_swap
  given: {α β γ : Type*} {f : α -> γ} {g : β -> γ}
  proof: by
  grind

中文:
定理 elim_swap
  条件: {α β γ : 类型} {f : α -> γ} {g : β -> γ}
  证明: by
  grind
-/
theorem elim_swap {α β γ : Type*} {f : α -> γ} {g : β -> γ} :
    Sum.elim f g ∘ Sum.swap = Sum.elim g f := by
  grind

-- Lean has removed the `@[simp]` attribute on these. For now Mathlib adds it back.
attribute [simp] Sum.forall Sum.exists

/--
theorem `exists_sum` / 定理 `exists_sum`

English:
theorem exists_sum
  given: {γ : α oplus β -> Sort*} (p : (forall ab, γ ab) -> Prop)
  proof: by
  rw [← not_forall_not]; rw [forall_sum]
  simp

中文:
定理 exists_sum
  条件: {γ : α oplus β -> Sort*} (p : (对任意 ab, γ ab) -> 命题)
  证明: by
  rw [← not_forall_not]; rw [forall_sum]
  simp

Depends on / 依赖: forall_sum, not_forall_not
-/
theorem exists_sum {γ : α oplus β -> Sort*} (p : (forall ab, γ ab) -> Prop) :
    (exists fab, p fab) ↔ (exists fa fb, p (Sum.rec fa fb)) := by
  rw [← not_forall_not]; rw [forall_sum]
  simp

/--
theorem `inl_injective` / 定理 `inl_injective`

English:
theorem inl_injective
  statement: Function.Injective (inl : α -> α oplus β)
  proof: fun _ _ => inl.inj

中文:
定理 inl_injective
  结论: Function.Injective (inl : α -> α oplus β)
  证明: fun _ _ => inl.inj

Depends on / 依赖: inl.inj
-/
theorem inl_injective : Function.Injective (inl : α -> α oplus β) := fun _ _ => inl.inj

/--
theorem `inr_injective` / 定理 `inr_injective`

English:
theorem inr_injective
  statement: Function.Injective (inr : β -> α oplus β)
  proof: fun _ _ => inr.inj

中文:
定理 inr_injective
  结论: Function.Injective (inr : β -> α oplus β)
  证明: fun _ _ => inr.inj

Depends on / 依赖: inr.inj
-/
theorem inr_injective : Function.Injective (inr : β -> α oplus β) := fun _ _ => inr.inj

/--
theorem `sum_rec_congr` / 定理 `sum_rec_congr`

English:
theorem sum_rec_congr
  statement: (P : α oplus β -> Sort*) (f : forall i, P (inl i)) (g : forall i, P (inr i))
  proof: by cases h; rfl

中文:
定理 sum_rec_congr
  结论: (P : α oplus β -> Sort*) (f : 对任意 i, P (inl i)) (g : 对任意 i, P (inr i))
  证明: by cases h; rfl
-/
theorem sum_rec_congr (P : α oplus β -> Sort*) (f : forall i, P (inl i)) (g : forall i, P (inr i))
    {x y : α oplus β} (h : x = y) :
    @Sum.rec _ _ _ f g x = cast (congr_arg P h.symm) (@Sum.rec _ _ _ f g y) := by cases h; rfl

section get

variable {x : α oplus β}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eq_left_iff_getLeft_eq` / 定理 `eq_left_iff_getLeft_eq`

English:
theorem eq_left_iff_getLeft_eq
  given: {a : α}
  statement: x = inl a ↔ exists h, x.getLeft h = a
  proof: by
  cases x <;> simp

中文:
定理 eq_left_iff_getLeft_eq
  条件: {a : α}
  结论: x = inl a ↔ 存在 h, x.getLeft h = a
  证明: by
  cases x <;> simp
-/
theorem eq_left_iff_getLeft_eq {a : α} : x = inl a ↔ exists h, x.getLeft h = a := by
  cases x <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eq_right_iff_getRight_eq` / 定理 `eq_right_iff_getRight_eq`

English:
theorem eq_right_iff_getRight_eq
  given: {b : β}
  statement: x = inr b ↔ exists h, x.getRight h = b
  proof: by
  cases x <;> simp

中文:
定理 eq_right_iff_getRight_eq
  条件: {b : β}
  结论: x = inr b ↔ 存在 h, x.getRight h = b
  证明: by
  cases x <;> simp
-/
theorem eq_right_iff_getRight_eq {b : β} : x = inr b ↔ exists h, x.getRight h = b := by
  cases x <;> simp

/--
theorem `getLeft_eq_getLeft?` / 定理 `getLeft_eq_getLeft?`

English:
theorem getLeft_eq_getLeft?
  given: (h₁ : x.isLeft) (h₂ : x.getLeft?.isSome)
  proof: by grind

中文:
定理 getLeft_eq_getLeft?
  条件: (h₁ : x.isLeft) (h₂ : x.getLeft?.isSome)
  证明: by grind
-/
theorem getLeft_eq_getLeft? (h₁ : x.isLeft) (h₂ : x.getLeft?.isSome) :
    x.getLeft h₁ = x.getLeft?.get h₂ := by grind

/--
theorem `getRight_eq_getRight?` / 定理 `getRight_eq_getRight?`

English:
theorem getRight_eq_getRight?
  given: (h₁ : x.isRight) (h₂ : x.getRight?.isSome)
  proof: by grind

中文:
定理 getRight_eq_getRight?
  条件: (h₁ : x.isRight) (h₂ : x.getRight?.isSome)
  证明: by grind
-/
theorem getRight_eq_getRight? (h₁ : x.isRight) (h₂ : x.getRight?.isSome) :
    x.getRight h₁ = x.getRight?.get h₂ := by grind

/--
theorem `isSome_getLeft?_iff_isLeft` / 定理 `isSome_getLeft?_iff_isLeft`

English:
theorem isSome_getLeft?_iff_isLeft
  statement: x.getLeft?.isSome ↔ x.isLeft
  proof: by
  grind

中文:
定理 isSome_getLeft?_iff_isLeft
  结论: x.getLeft?.isSome ↔ x.isLeft
  证明: by
  grind
-/
@[simp] theorem isSome_getLeft?_iff_isLeft : x.getLeft?.isSome ↔ x.isLeft := by
  grind

/--
theorem `isSome_getRight?_iff_isRight` / 定理 `isSome_getRight?_iff_isRight`

English:
theorem isSome_getRight?_iff_isRight
  statement: x.getRight?.isSome ↔ x.isRight
  proof: by
  grind

中文:
定理 isSome_getRight?_iff_isRight
  结论: x.getRight?.isSome ↔ x.isRight
  证明: by
  grind
-/
@[simp] theorem isSome_getRight?_iff_isRight : x.getRight?.isSome ↔ x.isRight := by
  grind

end get

open Function (update update_eq_iff update_comp_eq_of_injective update_comp_eq_of_forall_ne)

@[simp]
/--
theorem `update_elim_inl` / 定理 `update_elim_inl`

English:
theorem update_elim_inl
  statement: [DecidableEq α] [DecidableEq (α oplus β)] {f : α -> γ} {g : β -> γ} {i : α}
  proof: update_eq_iff.2 ⟨by simp, by simp +contextual⟩

@[simp]

中文:
定理 update_elim_inl
  结论: [DecidableEq α] [DecidableEq (α oplus β)] {f : α -> γ} {g : β -> γ} {i : α}
  证明: update_eq_iff.2 ⟨by simp, by simp +contextual⟩

@[simp]

Depends on / 依赖: contextual, update_eq_iff
-/
theorem update_elim_inl [DecidableEq α] [DecidableEq (α oplus β)] {f : α -> γ} {g : β -> γ} {i : α}
    {x : γ} : update (Sum.elim f g) (inl i) x = Sum.elim (update f i x) g :=
  update_eq_iff.2 ⟨by simp, by simp +contextual⟩

@[simp]
/--
theorem `update_elim_inr` / 定理 `update_elim_inr`

English:
theorem update_elim_inr
  statement: [DecidableEq β] [DecidableEq (α oplus β)] {f : α -> γ} {g : β -> γ} {i : β}
  proof: update_eq_iff.2 ⟨by simp, by simp +contextual⟩

@[simp]

中文:
定理 update_elim_inr
  结论: [DecidableEq β] [DecidableEq (α oplus β)] {f : α -> γ} {g : β -> γ} {i : β}
  证明: update_eq_iff.2 ⟨by simp, by simp +contextual⟩

@[simp]

Depends on / 依赖: contextual, update_eq_iff
-/
theorem update_elim_inr [DecidableEq β] [DecidableEq (α oplus β)] {f : α -> γ} {g : β -> γ} {i : β}
    {x : γ} : update (Sum.elim f g) (inr i) x = Sum.elim f (update g i x) :=
  update_eq_iff.2 ⟨by simp, by simp +contextual⟩

@[simp]
/--
theorem `update_inl_comp_inl` / 定理 `update_inl_comp_inl`

English:
theorem update_inl_comp_inl
  statement: [DecidableEq α] [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α}
  proof: update_comp_eq_of_injective _ inl_injective _ _

@[simp]

中文:
定理 update_inl_comp_inl
  结论: [DecidableEq α] [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α}
  证明: update_comp_eq_of_injective _ inl_injective _ _

@[simp]

Depends on / 依赖: inl_injective, update_comp_eq_of_injective
-/
theorem update_inl_comp_inl [DecidableEq α] [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α}
    {x : γ} : update f (inl i) x ∘ inl = update (f ∘ inl) i x :=
  update_comp_eq_of_injective _ inl_injective _ _

@[simp]
/--
theorem `update_inl_apply_inl` / 定理 `update_inl_apply_inl`

English:
theorem update_inl_apply_inl
  statement: [DecidableEq α] [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i j : α}
  proof: by
  grind

@[simp]

中文:
定理 update_inl_apply_inl
  结论: [DecidableEq α] [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i j : α}
  证明: by
  grind

@[simp]
-/
theorem update_inl_apply_inl [DecidableEq α] [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i j : α}
    {x : γ} : update f (inl i) x (inl j) = update (f ∘ inl) i x j := by
  grind

@[simp]
/--
theorem `update_inl_comp_inr` / 定理 `update_inl_comp_inr`

English:
theorem update_inl_comp_inr
  given: [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α} {x : γ}
  proof: (update_comp_eq_of_forall_ne _ _) fun _ => inr_ne_inl

中文:
定理 update_inl_comp_inr
  条件: [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α} {x : γ}
  证明: (update_comp_eq_of_forall_ne _ _) fun _ => inr_ne_inl

Depends on / 依赖: inr_ne_inl, update_comp_eq_of_forall_ne
-/
theorem update_inl_comp_inr [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α} {x : γ} :
    update f (inl i) x ∘ inr = f ∘ inr :=
  (update_comp_eq_of_forall_ne _ _) fun _ => inr_ne_inl

/--
theorem `update_inl_apply_inr` / 定理 `update_inl_apply_inr`

English:
theorem update_inl_apply_inr
  given: [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α} {j : β} {x : γ}
  proof: Function.update_of_ne inr_ne_inl ..

@[simp]

中文:
定理 update_inl_apply_inr
  条件: [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α} {j : β} {x : γ}
  证明: Function.update_of_ne inr_ne_inl ..

@[simp]

Depends on / 依赖: Function, Function.update_of_ne, inr_ne_inl, update_of_ne
-/
theorem update_inl_apply_inr [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α} {j : β} {x : γ} :
    update f (inl i) x (inr j) = f (inr j) :=
  Function.update_of_ne inr_ne_inl ..

@[simp]
/--
theorem `update_inr_comp_inl` / 定理 `update_inr_comp_inl`

English:
theorem update_inr_comp_inl
  given: [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : β} {x : γ}
  proof: (update_comp_eq_of_forall_ne _ _) fun _ => inl_ne_inr

中文:
定理 update_inr_comp_inl
  条件: [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : β} {x : γ}
  证明: (update_comp_eq_of_forall_ne _ _) fun _ => inl_ne_inr

Depends on / 依赖: inl_ne_inr, update_comp_eq_of_forall_ne
-/
theorem update_inr_comp_inl [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : β} {x : γ} :
    update f (inr i) x ∘ inl = f ∘ inl :=
  (update_comp_eq_of_forall_ne _ _) fun _ => inl_ne_inr

/--
theorem `update_inr_apply_inl` / 定理 `update_inr_apply_inl`

English:
theorem update_inr_apply_inl
  given: [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α} {j : β} {x : γ}
  proof: Function.update_of_ne inl_ne_inr ..

@[simp]

中文:
定理 update_inr_apply_inl
  条件: [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α} {j : β} {x : γ}
  证明: Function.update_of_ne inl_ne_inr ..

@[simp]

Depends on / 依赖: Function, Function.update_of_ne, inl_ne_inr, update_of_ne
-/
theorem update_inr_apply_inl [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α} {j : β} {x : γ} :
    update f (inr j) x (inl i) = f (inl i) :=
  Function.update_of_ne inl_ne_inr ..

@[simp]
/--
theorem `update_inr_comp_inr` / 定理 `update_inr_comp_inr`

English:
theorem update_inr_comp_inr
  statement: [DecidableEq β] [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : β}
  proof: update_comp_eq_of_injective _ inr_injective _ _

@[simp]

中文:
定理 update_inr_comp_inr
  结论: [DecidableEq β] [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : β}
  证明: update_comp_eq_of_injective _ inr_injective _ _

@[simp]

Depends on / 依赖: inr_injective, update_comp_eq_of_injective
-/
theorem update_inr_comp_inr [DecidableEq β] [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : β}
    {x : γ} : update f (inr i) x ∘ inr = update (f ∘ inr) i x :=
  update_comp_eq_of_injective _ inr_injective _ _

@[simp]
/--
theorem `update_inr_apply_inr` / 定理 `update_inr_apply_inr`

English:
theorem update_inr_apply_inr
  statement: [DecidableEq β] [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i j : β}
  proof: by
  rw [← update_inr_comp_inr]; rw [Function.comp_apply]

@[simp]

中文:
定理 update_inr_apply_inr
  结论: [DecidableEq β] [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i j : β}
  证明: by
  rw [← update_inr_comp_inr]; rw [Function.comp_apply]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, update_inr_comp_inr
-/
theorem update_inr_apply_inr [DecidableEq β] [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i j : β}
    {x : γ} : update f (inr i) x (inr j) = update (f ∘ inr) i x j := by
  rw [← update_inr_comp_inr]; rw [Function.comp_apply]

@[simp]
/--
theorem `update_inl_apply_inl'` / 定理 `update_inl_apply_inl'`

English:
theorem update_inl_apply_inl'
  statement: {γ : α oplus β -> Type*} [DecidableEq α] [DecidableEq (α oplus β)]
  proof: Function.update_apply_of_injective f Sum.inl_injective i x j

@[simp]

中文:
定理 update_inl_apply_inl'
  结论: {γ : α oplus β -> 类型} [DecidableEq α] [DecidableEq (α oplus β)]
  证明: Function.update_apply_of_injective f Sum.inl_injective i x j

@[simp]

Depends on / 依赖: Function, Function.update_apply_of_injective, Sum.inl_injective, inl_injective, update_apply_of_injective
-/
theorem update_inl_apply_inl' {γ : α oplus β -> Type*} [DecidableEq α] [DecidableEq (α oplus β)]
    {f : (i : α oplus β) -> γ i} {i : α} {x : γ (.inl i)} (j : α) :
    update f (.inl i) x (Sum.inl j) = update (fun j => f (.inl j)) i x j :=
  Function.update_apply_of_injective f Sum.inl_injective i x j

@[simp]
/--
theorem `update_inr_apply_inr'` / 定理 `update_inr_apply_inr'`

English:
theorem update_inr_apply_inr'
  statement: {γ : α oplus β -> Type*} [DecidableEq β] [DecidableEq (α oplus β)]
  proof: Function.update_apply_of_injective f Sum.inr_injective i x j

@[simp]

中文:
定理 update_inr_apply_inr'
  结论: {γ : α oplus β -> 类型} [DecidableEq β] [DecidableEq (α oplus β)]
  证明: Function.update_apply_of_injective f Sum.inr_injective i x j

@[simp]

Depends on / 依赖: Function, Function.update_apply_of_injective, Sum.inr_injective, inr_injective, update_apply_of_injective
-/
theorem update_inr_apply_inr' {γ : α oplus β -> Type*} [DecidableEq β] [DecidableEq (α oplus β)]
    {f : (i : α oplus β) -> γ i} {i : β} {x : γ (.inr i)} (j : β) :
    update f (.inr i) x (Sum.inr j) = update (fun j => f (.inr j)) i x j :=
  Function.update_apply_of_injective f Sum.inr_injective i x j

@[simp]
/--
lemma `rec_update_left` / 引理 `rec_update_left`

English:
lemma rec_update_left
  statement: {γ : α oplus β -> Sort*} [DecidableEq α] [DecidableEq β]
  proof: Function.rec_update Sum.inl_injective (Sum.rec · g) (fun _ _ => rfl) (fun
    | _, _, .inl _, h => (h _ rfl).elim
    | _, _, .inr _, _ => rfl) _ _ _

@[simp]

中文:
引理 rec_update_left
  结论: {γ : α oplus β -> Sort*} [DecidableEq α] [DecidableEq β]
  证明: Function.rec_update Sum.inl_injective (Sum.rec · g) (fun _ _ => rfl) (fun
    | _, _, .inl _, h => (h _ rfl).elim
    | _, _, .inr _, _ => rfl) _ _ _

@[simp]

Depends on / 依赖: Function, Function.rec_update, Sum.inl_injective, Sum.rec, inl_injective, rec_update
-/
lemma rec_update_left {γ : α oplus β -> Sort*} [DecidableEq α] [DecidableEq β]
    (f : forall a, γ (.inl a)) (g : forall b, γ (.inr b)) (a : α) (x : γ (.inl a)) :
    Sum.rec (update f a x) g = update (Sum.rec f g) (.inl a) x :=
  Function.rec_update Sum.inl_injective (Sum.rec · g) (fun _ _ => rfl) (fun
    | _, _, .inl _, h => (h _ rfl).elim
    | _, _, .inr _, _ => rfl) _ _ _

@[simp]
/--
lemma `rec_update_right` / 引理 `rec_update_right`

English:
lemma rec_update_right
  statement: {γ : α oplus β -> Sort*} [DecidableEq α] [DecidableEq β]
  proof: Function.rec_update Sum.inr_injective (Sum.rec f) (fun _ _ => rfl) (fun
    | _, _, .inr _, h => (h _ rfl).elim
    | _, _, .inl _, _ => rfl) _ _ _

@[simp]

中文:
引理 rec_update_right
  结论: {γ : α oplus β -> Sort*} [DecidableEq α] [DecidableEq β]
  证明: Function.rec_update Sum.inr_injective (Sum.rec f) (fun _ _ => rfl) (fun
    | _, _, .inr _, h => (h _ rfl).elim
    | _, _, .inl _, _ => rfl) _ _ _

@[simp]

Depends on / 依赖: Function, Function.rec_update, Sum.inr_injective, Sum.rec, inr_injective, rec_update
-/
lemma rec_update_right {γ : α oplus β -> Sort*} [DecidableEq α] [DecidableEq β]
    (f : forall a, γ (.inl a)) (g : forall b, γ (.inr b)) (b : β) (x : γ (.inr b)) :
    Sum.rec f (update g b x) = update (Sum.rec f g) (.inr b) x :=
  Function.rec_update Sum.inr_injective (Sum.rec f) (fun _ _ => rfl) (fun
    | _, _, .inr _, h => (h _ rfl).elim
    | _, _, .inl _, _ => rfl) _ _ _

@[simp]
/--
lemma `elim_update_left` / 引理 `elim_update_left`

English:
lemma elim_update_left
  statement: {γ : Sort*} [DecidableEq α] [DecidableEq β]
  proof: rec_update_left _ _ _ _

@[simp]

中文:
引理 elim_update_left
  结论: {γ : Sort*} [DecidableEq α] [DecidableEq β]
  证明: rec_update_left _ _ _ _

@[simp]

Depends on / 依赖: rec_update_left
-/
lemma elim_update_left {γ : Sort*} [DecidableEq α] [DecidableEq β]
    (f : α -> γ) (g : β -> γ) (a : α) (x : γ) :
    Sum.elim (update f a x) g = update (Sum.elim f g) (.inl a) x :=
  rec_update_left _ _ _ _

@[simp]
/--
lemma `elim_update_right` / 引理 `elim_update_right`

English:
lemma elim_update_right
  statement: {γ : Sort*} [DecidableEq α] [DecidableEq β]
  proof: rec_update_right _ _ _ _

@[simp]

中文:
引理 elim_update_right
  结论: {γ : Sort*} [DecidableEq α] [DecidableEq β]
  证明: rec_update_right _ _ _ _

@[simp]

Depends on / 依赖: rec_update_right
-/
lemma elim_update_right {γ : Sort*} [DecidableEq α] [DecidableEq β]
    (f : α -> γ) (g : β -> γ) (b : β) (x : γ) :
    Sum.elim f (update g b x) = update (Sum.elim f g) (.inr b) x :=
  rec_update_right _ _ _ _

@[simp]
/--
theorem `swap_leftInverse` / 定理 `swap_leftInverse`

English:
theorem swap_leftInverse
  statement: Function.LeftInverse (@swap α β) swap
  proof: swap_swap

@[simp]

中文:
定理 swap_leftInverse
  结论: Function.LeftInverse (@swap α β) swap
  证明: swap_swap

@[simp]

Depends on / 依赖: swap_swap
-/
theorem swap_leftInverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap

@[simp]
/--
theorem `swap_rightInverse` / 定理 `swap_rightInverse`

English:
theorem swap_rightInverse
  statement: Function.RightInverse (@swap α β) swap
  proof: swap_swap

mk_iff_of_inductive_prop Sum.LiftRel Sum.liftRel_iff

中文:
定理 swap_rightInverse
  结论: Function.RightInverse (@swap α β) swap
  证明: swap_swap

mk_iff_of_inductive_prop Sum.LiftRel Sum.liftRel_iff

Depends on / 依赖: swap_swap
-/
theorem swap_rightInverse : Function.RightInverse (@swap α β) swap :=
  swap_swap

mk_iff_of_inductive_prop Sum.LiftRel Sum.liftRel_iff

namespace LiftRel

variable {r : α -> γ -> Prop} {s : β -> δ -> Prop} {x : α oplus β} {y : γ oplus δ}
  {a : α} {b : β} {c : γ} {d : δ}

/--
theorem `isLeft_congr` / 定理 `isLeft_congr`

English:
theorem isLeft_congr
  given: (h : LiftRel r s x y)
  statement: x.isLeft ↔ y.isLeft
  proof: by cases h <;> rfl

中文:
定理 isLeft_congr
  条件: (h : LiftRel r s x y)
  结论: x.isLeft ↔ y.isLeft
  证明: by cases h <;> rfl
-/
theorem isLeft_congr (h : LiftRel r s x y) : x.isLeft ↔ y.isLeft := by cases h <;> rfl
/--
theorem `isRight_congr` / 定理 `isRight_congr`

English:
theorem isRight_congr
  given: (h : LiftRel r s x y)
  statement: x.isRight ↔ y.isRight
  proof: by cases h <;> rfl

中文:
定理 isRight_congr
  条件: (h : LiftRel r s x y)
  结论: x.isRight ↔ y.isRight
  证明: by cases h <;> rfl
-/
theorem isRight_congr (h : LiftRel r s x y) : x.isRight ↔ y.isRight := by cases h <;> rfl

/--
theorem `isLeft_left` / 定理 `isLeft_left`

English:
theorem isLeft_left
  given: (h : LiftRel r s x (inl c))
  statement: x.isLeft
  proof: by cases h; rfl

中文:
定理 isLeft_left
  条件: (h : LiftRel r s x (inl c))
  结论: x.isLeft
  证明: by cases h; rfl
-/
theorem isLeft_left (h : LiftRel r s x (inl c)) : x.isLeft := by cases h; rfl
/--
theorem `isLeft_right` / 定理 `isLeft_right`

English:
theorem isLeft_right
  given: (h : LiftRel r s (inl a) y)
  statement: y.isLeft
  proof: by cases h; rfl

中文:
定理 isLeft_right
  条件: (h : LiftRel r s (inl a) y)
  结论: y.isLeft
  证明: by cases h; rfl
-/
theorem isLeft_right (h : LiftRel r s (inl a) y) : y.isLeft := by cases h; rfl
/--
theorem `isRight_left` / 定理 `isRight_left`

English:
theorem isRight_left
  given: (h : LiftRel r s x (inr d))
  statement: x.isRight
  proof: by cases h; rfl

中文:
定理 isRight_left
  条件: (h : LiftRel r s x (inr d))
  结论: x.isRight
  证明: by cases h; rfl
-/
theorem isRight_left (h : LiftRel r s x (inr d)) : x.isRight := by cases h; rfl
/--
theorem `isRight_right` / 定理 `isRight_right`

English:
theorem isRight_right
  given: (h : LiftRel r s (inr b) y)
  statement: y.isRight
  proof: by cases h; rfl

中文:
定理 isRight_right
  条件: (h : LiftRel r s (inr b) y)
  结论: y.isRight
  证明: by cases h; rfl
-/
theorem isRight_right (h : LiftRel r s (inr b) y) : y.isRight := by cases h; rfl

/--
theorem `exists_of_isLeft_left` / 定理 `exists_of_isLeft_left`

English:
theorem exists_of_isLeft_left
  given: (h₁ : LiftRel r s x y) (h₂ : x.isLeft)
  proof: by
  grind

中文:
定理 exists_of_isLeft_left
  条件: (h₁ : LiftRel r s x y) (h₂ : x.isLeft)
  证明: by
  grind
-/
theorem exists_of_isLeft_left (h₁ : LiftRel r s x y) (h₂ : x.isLeft) :
    exists a c, r a c ∧ x = inl a ∧ y = inl c := by
  grind

/--
theorem `exists_of_isLeft_right` / 定理 `exists_of_isLeft_right`

English:
theorem exists_of_isLeft_right
  given: (h₁ : LiftRel r s x y) (h₂ : y.isLeft)
  proof: exists_of_isLeft_left h₁ ((isLeft_congr h₁).mpr h₂)

中文:
定理 exists_of_isLeft_right
  条件: (h₁ : LiftRel r s x y) (h₂ : y.isLeft)
  证明: exists_of_isLeft_left h₁ ((isLeft_congr h₁).mpr h₂)

Depends on / 依赖: exists_of_isLeft_left, isLeft_congr
-/
theorem exists_of_isLeft_right (h₁ : LiftRel r s x y) (h₂ : y.isLeft) :
    exists a c, r a c ∧ x = inl a ∧ y = inl c := exists_of_isLeft_left h₁ ((isLeft_congr h₁).mpr h₂)

/--
theorem `exists_of_isRight_left` / 定理 `exists_of_isRight_left`

English:
theorem exists_of_isRight_left
  given: (h₁ : LiftRel r s x y) (h₂ : x.isRight)
  proof: by
  grind

中文:
定理 exists_of_isRight_left
  条件: (h₁ : LiftRel r s x y) (h₂ : x.isRight)
  证明: by
  grind
-/
theorem exists_of_isRight_left (h₁ : LiftRel r s x y) (h₂ : x.isRight) :
    exists b d, s b d ∧ x = inr b ∧ y = inr d := by
  grind

/--
theorem `exists_of_isRight_right` / 定理 `exists_of_isRight_right`

English:
theorem exists_of_isRight_right
  given: (h₁ : LiftRel r s x y) (h₂ : y.isRight)
  proof: exists_of_isRight_left h₁ ((isRight_congr h₁).mpr h₂)

中文:
定理 exists_of_isRight_right
  条件: (h₁ : LiftRel r s x y) (h₂ : y.isRight)
  证明: exists_of_isRight_left h₁ ((isRight_congr h₁).mpr h₂)

Depends on / 依赖: exists_of_isRight_left, isRight_congr
-/
theorem exists_of_isRight_right (h₁ : LiftRel r s x y) (h₂ : y.isRight) :
    exists b d, s b d ∧ x = inr b ∧ y = inr d :=
  exists_of_isRight_left h₁ ((isRight_congr h₁).mpr h₂)

end LiftRel

end Sum

open Sum

namespace Function

/--
theorem `Injective.sumElim` / 定理 `Injective.sumElim`

English:
theorem Injective.sumElim
  statement: {γ : Sort*} {f : α -> γ} {g : β -> γ} (hf : Injective f) (hg : Injective g)

中文:
定理 Injective.sumElim
  结论: {γ : Sort*} {f : α -> γ} {g : β -> γ} (hf : Injective f) (hg : Injective g)
-/
theorem Injective.sumElim {γ : Sort*} {f : α -> γ} {g : β -> γ} (hf : Injective f) (hg : Injective g)
    (hfg : forall a b, f a != g b) : Injective (Sum.elim f g)
| inl _, inl _, h => congr_arg inl hf h
  | inl _, inr _, h => (hfg _ _ h).elim
  | inr _, inl _, h => (hfg _ _ h.symm).elim
| inr _, inr _, h => congr_arg inr hg h

/--
theorem `Injective.sumMap` / 定理 `Injective.sumMap`

English:
theorem Injective.sumMap
  given: {f : α -> β} {g : α' -> β'} (hf : Injective f) (hg : Injective g)

中文:
定理 Injective.sumMap
  条件: {f : α -> β} {g : α' -> β'} (hf : Injective f) (hg : Injective g)
-/
theorem Injective.sumMap {f : α -> β} {g : α' -> β'} (hf : Injective f) (hg : Injective g) :
    Injective (Sum.map f g)
| inl _, inl _, h => congr_arg inl hf inl.inj h
| inr _, inr _, h => congr_arg inr hg inr.inj h

/--
theorem `Surjective.sumMap` / 定理 `Surjective.sumMap`

English:
theorem Surjective.sumMap
  given: {f : α -> β} {g : α' -> β'} (hf : Surjective f) (hg : Surjective g)
  proof: hf y
    ⟨inl x, congr_arg inl hx⟩
  | inr y =>
    let ⟨x, hx⟩ := hg y
    ⟨inr x, congr_arg inr hx⟩

中文:
定理 Surjective.sumMap
  条件: {f : α -> β} {g : α' -> β'} (hf : Surjective f) (hg : Surjective g)
  证明: hf y
    ⟨inl x, congr_arg inl hx⟩
  | inr y =>
    let ⟨x, hx⟩ := hg y
    ⟨inr x, congr_arg inr hx⟩
-/
theorem Surjective.sumMap {f : α -> β} {g : α' -> β'} (hf : Surjective f) (hg : Surjective g) :
    Surjective (Sum.map f g)
  | inl y =>
    let ⟨x, hx⟩ := hf y
    ⟨inl x, congr_arg inl hx⟩
  | inr y =>
    let ⟨x, hx⟩ := hg y
    ⟨inr x, congr_arg inr hx⟩

/--
theorem `Bijective.sumMap` / 定理 `Bijective.sumMap`

English:
theorem Bijective.sumMap
  given: {f : α -> β} {g : α' -> β'} (hf : Bijective f) (hg : Bijective g)
  proof: ⟨hf.injective.sumMap hg.injective, hf.surjective.sumMap hg.surjective⟩

中文:
定理 Bijective.sumMap
  条件: {f : α -> β} {g : α' -> β'} (hf : Bijective f) (hg : Bijective g)
  证明: ⟨hf.injective.sumMap hg.injective, hf.surjective.sumMap hg.surjective⟩

Depends on / 依赖: hf.injective.sumMap, hf.surjective.sumMap, hg.injective, hg.surjective, injective, sumMap, surjective
-/
theorem Bijective.sumMap {f : α -> β} {g : α' -> β'} (hf : Bijective f) (hg : Bijective g) :
    Bijective (Sum.map f g) :=
  ⟨hf.injective.sumMap hg.injective, hf.surjective.sumMap hg.surjective⟩

end Function

namespace Sum

open Function

@[simp]
/--
theorem `elim_injective` / 定理 `elim_injective`

English:
theorem elim_injective
  given: {γ : Sort*} {f : α -> γ} {g : β -> γ}
  proof: ⟨h.comp inl_injective, h.comp inr_injective, fun _ _ => h.ne inl_ne_inr⟩
  mpr | ⟨hf, hg, hfg⟩ => hf.sumElim hg hfg

@[simp]

中文:
定理 elim_injective
  条件: {γ : Sort*} {f : α -> γ} {g : β -> γ}
  证明: ⟨h.comp inl_injective, h.comp inr_injective, fun _ _ => h.ne inl_ne_inr⟩
  mpr | ⟨hf, hg, hfg⟩ => hf.sumElim hg hfg

@[simp]

Depends on / 依赖: h.comp, h.ne, inl_injective, inl_ne_inr, inr_injective
-/
theorem elim_injective {γ : Sort*} {f : α -> γ} {g : β -> γ} :
    Injective (Sum.elim f g) ↔ Injective f ∧ Injective g ∧ forall a b, f a != g b where
  mp h := ⟨h.comp inl_injective, h.comp inr_injective, fun _ _ => h.ne inl_ne_inr⟩
  mpr | ⟨hf, hg, hfg⟩ => hf.sumElim hg hfg

@[simp]
/--
theorem `elim_injective'` / 定理 `elim_injective'`

English:
theorem elim_injective'
  given: {γ : Sort*} {f : α -> γ}
  proof: fun g₁ g₂ hg => funext fun b => by simpa using congr_fun hg (Sum.inr b)

@[simp]

中文:
定理 elim_injective'
  条件: {γ : Sort*} {f : α -> γ}
  证明: fun g₁ g₂ hg => funext fun b => by simpa using congr_fun hg (Sum.inr b)

@[simp]

Depends on / 依赖: Sum.inr, congr_fun
-/
theorem elim_injective' {γ : Sort*} {f : α -> γ} :
    Injective (Sum.elim f : (β -> γ) -> (α oplus β -> γ)) :=
  fun g₁ g₂ hg => funext fun b => by simpa using congr_fun hg (Sum.inr b)

@[simp]
/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : α -> γ} {g : β -> δ}
  proof: ⟨.of_comp h.comp inl_injective, .of_comp h.comp inr_injective⟩
  mpr | ⟨hf, hg⟩ => hf.sumMap hg

@[simp]

中文:
定理 map_injective
  条件: {f : α -> γ} {g : β -> δ}
  证明: ⟨.of_comp h.comp inl_injective, .of_comp h.comp inr_injective⟩
  mpr | ⟨hf, hg⟩ => hf.sumMap hg

@[simp]

Depends on / 依赖: h.comp, inl_injective, inr_injective, of_comp
-/
theorem map_injective {f : α -> γ} {g : β -> δ} :
    Injective (Sum.map f g) ↔ Injective f ∧ Injective g where
mp h := ⟨.of_comp h.comp inl_injective, .of_comp h.comp inr_injective⟩
  mpr | ⟨hf, hg⟩ => hf.sumMap hg

@[simp]
/--
theorem `map_surjective` / 定理 `map_surjective`

English:
theorem map_surjective
  given: {f : α -> γ} {g : β -> δ}
  proof: ⟨
      (fun c => by
        obtain ⟨a | b, h⟩ := h (inl c)
        · exact ⟨a, inl_injective h⟩
        · cases h),
      (fun d => by
        obtain ⟨a | b, h⟩ := h (inr d)
        · cases h
        · exact ⟨b, inr_injective h⟩)⟩
  mpr | ⟨hf, hg⟩ => hf.sumMap hg

@[simp]

中文:
定理 map_surjective
  条件: {f : α -> γ} {g : β -> δ}
  证明: ⟨
      (fun c => by
        obtain ⟨a | b, h⟩ := h (inl c)
        · exact ⟨a, inl_injective h⟩
        · cases h),
      (fun d => by
        obtain ⟨a | b, h⟩ := h (inr d)
        · cases h
        · exact ⟨b, inr_injective h⟩)⟩
  mpr | ⟨hf, hg⟩ => hf.sumMap hg

@[simp]
-/
theorem map_surjective {f : α -> γ} {g : β -> δ} :
    Surjective (Sum.map f g) ↔ Surjective f ∧ Surjective g where
  mp h := ⟨
      (fun c => by
        obtain ⟨a | b, h⟩ := h (inl c)
        · exact ⟨a, inl_injective h⟩
        · cases h),
      (fun d => by
        obtain ⟨a | b, h⟩ := h (inr d)
        · cases h
        · exact ⟨b, inr_injective h⟩)⟩
  mpr | ⟨hf, hg⟩ => hf.sumMap hg

@[simp]
/--
theorem `map_bijective` / 定理 `map_bijective`

English:
theorem map_bijective
  given: {f : α -> γ} {g : β -> δ}
  proof: (map_injective.and map_surjective).trans and_and_and_comm

中文:
定理 map_bijective
  条件: {f : α -> γ} {g : β -> δ}
  证明: (map_injective.and map_surjective).trans and_and_and_comm

Depends on / 依赖: and_and_and_comm, map_injective, map_injective.and, map_surjective
-/
theorem map_bijective {f : α -> γ} {g : β -> δ} :
    Bijective (Sum.map f g) ↔ Bijective f ∧ Bijective g :=
(map_injective.and map_surjective).trans and_and_and_comm

end Sum

/-!
### Ternary sum

Abbreviations for the maps from the summands to `α ⊕ β ⊕ γ`. This is useful for pattern-matching.
-/

namespace Sum3

/-- The map from the first summand into a ternary sum. -/
@[match_pattern, simp, reducible]
/--
Definition of `in₀` / `in₀` 的定义

English:
definition in₀
  signature: (a : α)
  body: inl a

中文:
定义 in₀
  签名: (a : α)
  定义体: inl a
-/
def in₀ (a : α) : α oplus (β oplus γ) :=
  inl a

/-- The map from the second summand into a ternary sum. -/
@[match_pattern, simp, reducible]
/--
Definition of `in₁` / `in₁` 的定义

English:
definition in₁
  signature: (b : β)
  body: inr inl b

中文:
定义 in₁
  签名: (b : β)
  定义体: inr inl b
-/
def in₁ (b : β) : α oplus (β oplus γ) :=
inr inl b

/-- The map from the third summand into a ternary sum. -/
@[match_pattern, simp, reducible]
/--
Definition of `in₂` / `in₂` 的定义

English:
definition in₂
  signature: (c : γ)
  body: inr inr c

中文:
定义 in₂
  签名: (c : γ)
  定义体: inr inr c
-/
def in₂ (c : γ) : α oplus (β oplus γ) :=
inr inr c

end Sum3

/-!
### PSum
-/

namespace PSum

variable {α β : Sort*}

/--
theorem `inl_injective` / 定理 `inl_injective`

English:
theorem inl_injective
  statement: Function.Injective (PSum.inl : α -> α oplus' β)
  proof: fun _ _ => inl.inj

中文:
定理 inl_injective
  结论: Function.Injective (PSum.inl : α -> α oplus' β)
  证明: fun _ _ => inl.inj

Depends on / 依赖: inl.inj
-/
theorem inl_injective : Function.Injective (PSum.inl : α -> α oplus' β) := fun _ _ => inl.inj

/--
theorem `inr_injective` / 定理 `inr_injective`

English:
theorem inr_injective
  statement: Function.Injective (PSum.inr : β -> α oplus' β)
  proof: fun _ _ => inr.inj

中文:
定理 inr_injective
  结论: Function.Injective (PSum.inr : β -> α oplus' β)
  证明: fun _ _ => inr.inj

Depends on / 依赖: inr.inj
-/
theorem inr_injective : Function.Injective (PSum.inr : β -> α oplus' β) := fun _ _ => inr.inj

end PSum
