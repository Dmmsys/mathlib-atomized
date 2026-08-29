/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Haitao Zhang
-/
module

public import Mathlib.Init

import Mathlib.Tactic.Attr.Register

/-!
# General operations on functions
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅

namespace Function

variable {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} {ζ : Sort u₅}

/--
lemma `flip_def` / 引理 `flip_def`

English:
lemma flip_def
  given: {f : α -> β -> φ}
  statement: flip f = fun b a => f a b
  proof: rfl

中文:
引理 flip_def
  条件: {f : α -> β -> φ}
  结论: flip f = fun b a => f a b
  证明: rfl
-/
lemma flip_def {f : α -> β -> φ} : flip f = fun b a => f a b := rfl

attribute [mfld_simps] id_comp comp_id

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : φ -> δ) (g : β -> φ) (h : α -> β)
  statement: (f ∘ g) ∘ h = f ∘ g ∘ h
  proof: rfl

中文:
定理 comp_assoc
  条件: (f : φ -> δ) (g : β -> φ) (h : α -> β)
  结论: (f ∘ g) ∘ h = f ∘ g ∘ h
  证明: rfl
-/
theorem comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) : (f ∘ g) ∘ h = f ∘ g ∘ h :=
  rfl

/- ### Dependent composition -/

/-- Composition of dependent functions: `(f ∘' g) x = f (g x)`, where type of `g x` depends on `x`
and type of `f (g x)` depends on `x` and `g x`. -/
@[inline, reducible]
/--
Definition of `dcomp` / `dcomp` 的定义

English:
definition dcomp
  signature: {β : α -> Sort u₂} {φ : forall {x : α}, β x -> Sort u₃} (f : forall {x : α} (y : β x), φ y)
  body: fun x => f (g x)

@[inherit_doc] infixr:80 " ∘' " => Function.dcomp

中文:
定义 dcomp
  签名: {β : α -> Sort u₂} {φ : 对任意 {x : α}, β x -> Sort u₃} (f : 对任意 {x : α} (y : β x), φ y)
  定义体: fun x => f (g x)

@[inherit_doc] infixr:80 " ∘' " => Function.dcomp
-/
def dcomp {β : α -> Sort u₂} {φ : forall {x : α}, β x -> Sort u₃} (f : forall {x : α} (y : β x), φ y)
    (g : forall x, β x) : forall x, φ (g x) := fun x => f (g x)

@[inherit_doc] infixr:80 " ∘' " => Function.dcomp

section DComp

variable {ι} {β : ι -> Sort*} {φ : forall {i : ι}, β i -> Sort*} (f : forall {i : ι} (y : β i), φ y)
    (g : forall i, β i) (i : ι)

/--
theorem `dcomp_def` / 定理 `dcomp_def`

English:
theorem dcomp_def
  statement: @f ∘' g = fun i => f (g i)
  proof: rfl

中文:
定理 dcomp_def
  结论: @f ∘' g = fun i => f (g i)
  证明: rfl
-/
theorem dcomp_def : @f ∘' g = fun i => f (g i) := rfl

/--
theorem `dcomp_apply` / 定理 `dcomp_apply`

English:
theorem dcomp_apply
  statement: dcomp @f g i = f (g i)
  proof: rfl

中文:
定理 dcomp_apply
  结论: dcomp @f g i = f (g i)
  证明: rfl
-/
theorem dcomp_apply : dcomp @f g i = f (g i) := rfl

/--
theorem `dcomp_eq_comp` / 定理 `dcomp_eq_comp`

English:
theorem dcomp_eq_comp
  given: {α β γ} (f : β -> γ) (g : α -> β)
  statement: f ∘' g = f ∘ g
  proof: rfl

中文:
定理 dcomp_eq_comp
  条件: {α β γ} (f : β -> γ) (g : α -> β)
  结论: f ∘' g = f ∘ g
  证明: rfl
-/
@[simp] theorem dcomp_eq_comp {α β γ} (f : β -> γ) (g : α -> β) : f ∘' g = f ∘ g := rfl

end DComp

/- ### The product of functions -/

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: {ι} {α β : ι -> Type*} (f : forall i, α i) (g : forall i, β i) (i : ι)
  body: (f i, g i)

中文:
定义 prod
  签名: {ι} {α β : ι -> 类型} (f : 对任意 i, α i) (g : 对任意 i, β i) (i : ι)
  定义体: (f i, g i)
-/
protected def prod {ι} {α β : ι -> Type*} (f : forall i, α i) (g : forall i, β i) (i : ι) :
    α i × β i := (f i, g i)

section DProd

variable {ι} {α β : ι -> Type*} (f f' : forall i, α i) (g g' : forall i, β i)

/--
theorem `prod_def` / 定理 `prod_def`

English:
theorem prod_def
  statement: Function.prod f g = fun i : ι => (f i, g i)
  proof: rfl

中文:
定理 prod_def
  结论: Function.prod f g = fun i : ι => (f i, g i)
  证明: rfl
-/
theorem prod_def : Function.prod f g = fun i : ι => (f i, g i) := rfl

/--
lemma `prod_apply` / 引理 `prod_apply`

English:
lemma prod_apply
  given: (i : ι)
  statement: Function.prod f g i = (f i, g i)
  proof: rfl

中文:
引理 prod_apply
  条件: (i : ι)
  结论: Function.prod f g i = (f i, g i)
  证明: rfl
-/
@[simp, grind =] lemma prod_apply (i : ι) : Function.prod f g i = (f i, g i) := rfl

variable {f f' g g'} in
/--
theorem `prod_inj` / 定理 `prod_inj`

English:
theorem prod_inj
  statement: Function.prod f g = Function.prod f' g' ↔ f = f' ∧ g = g'
  proof: by
  simp [funext_iff, Prod.ext_iff, forall_and]

中文:
定理 prod_inj
  结论: Function.prod f g = Function.prod f' g' ↔ f = f' ∧ g = g'
  证明: by
  simp [funext_iff, Prod.ext_iff, forall_and]
-/
@[simp] theorem prod_inj : Function.prod f g = Function.prod f' g' ↔ f = f' ∧ g = g' := by
  simp [funext_iff, Prod.ext_iff, forall_and]

end DProd

section Prod

variable {α β : Type*} {ι : Sort*} (f : ι -> α) (g : ι -> β)

/--
theorem `prod_ext_iff` / 定理 `prod_ext_iff`

English:
theorem prod_ext_iff
  given: {h h' : ι -> α × β}
  proof: prod_inj

中文:
定理 prod_ext_iff
  条件: {h h' : ι -> α × β}
  证明: prod_inj

Depends on / 依赖: prod_inj
-/
theorem prod_ext_iff {h h' : ι -> α × β} :
    h = h' ↔ Prod.fst ∘ h = Prod.fst ∘ h' ∧ Prod.snd ∘ h = Prod.snd ∘ h' :=
  prod_inj

/--
lemma `prod_fst_snd` / 引理 `prod_fst_snd`

English:
lemma prod_fst_snd
  statement: Function.prod (Prod.fst : _ -> α) (Prod.snd : _ -> β) = id
  proof: rfl

中文:
引理 prod_fst_snd
  结论: Function.prod (Prod.fst : _ -> α) (Prod.snd : _ -> β) = id
  证明: rfl
-/
@[simp] lemma prod_fst_snd : Function.prod (Prod.fst : _ -> α) (Prod.snd : _ -> β) = id := rfl
/--
lemma `prod_snd_fst` / 引理 `prod_snd_fst`

English:
lemma prod_snd_fst
  statement: Function.prod (Prod.snd : _ -> β) (Prod.fst : _ -> α) = .swap
  proof: rfl

中文:
引理 prod_snd_fst
  结论: Function.prod (Prod.snd : _ -> β) (Prod.fst : _ -> α) = .swap
  证明: rfl
-/
@[simp] lemma prod_snd_fst : Function.prod (Prod.snd : _ -> β) (Prod.fst : _ -> α) = .swap := rfl

/--
theorem `fst_comp_prod` / 定理 `fst_comp_prod`

English:
theorem fst_comp_prod
  statement: Prod.fst ∘ Function.prod f g = f
  proof: rfl

中文:
定理 fst_comp_prod
  结论: Prod.fst ∘ Function.prod f g = f
  证明: rfl
-/
@[simp] theorem fst_comp_prod : Prod.fst ∘ Function.prod f g = f := rfl
/--
theorem `snd_comp_prod` / 定理 `snd_comp_prod`

English:
theorem snd_comp_prod
  statement: Prod.snd ∘ Function.prod f g = g
  proof: rfl

中文:
定理 snd_comp_prod
  结论: Prod.snd ∘ Function.prod f g = g
  证明: rfl
-/
@[simp] theorem snd_comp_prod : Prod.snd ∘ Function.prod f g = g := rfl

/--
theorem `prod_fst_comp_snd_comp` / 定理 `prod_fst_comp_snd_comp`

English:
theorem prod_fst_comp_snd_comp
  given: (h : ι -> α × β)
  proof: rfl

中文:
定理 prod_fst_comp_snd_comp
  条件: (h : ι -> α × β)
  证明: rfl
-/
@[simp] theorem prod_fst_comp_snd_comp (h : ι -> α × β) :
    Function.prod (Prod.fst ∘ h) (Prod.snd ∘ h) = h := rfl

/--
theorem `const_prod` / 定理 `const_prod`

English:
theorem const_prod
  given: (p : α × β)
  statement: const ι p = Function.prod (const ι p.1) (const ι p.2)
  proof: rfl

中文:
定理 const_prod
  条件: (p : α × β)
  结论: const ι p = Function.prod (const ι p.1) (const ι p.2)
  证明: rfl
-/
theorem const_prod (p : α × β) : const ι p = Function.prod (const ι p.1) (const ι p.2) := rfl

/--
theorem `prod_const_const` / 定理 `prod_const_const`

English:
theorem prod_const_const
  given: (a : α) (b : β)
  proof: rfl

中文:
定理 prod_const_const
  条件: (a : α) (b : β)
  证明: rfl
-/
@[simp] theorem prod_const_const (a : α) (b : β) :
    Function.prod (const ι a) (const ι b) = const ι (a, b) := rfl

/--
theorem `prod_comp` / 定理 `prod_comp`

English:
theorem prod_comp
  given: {κ} (h : κ -> ι)
  statement: Function.prod f g ∘ h = Function.prod (f ∘ h) (g ∘ h)
  proof: rfl

中文:
定理 prod_comp
  条件: {κ} (h : κ -> ι)
  结论: Function.prod f g ∘ h = Function.prod (f ∘ h) (g ∘ h)
  证明: rfl
-/
theorem prod_comp {κ} (h : κ -> ι) : Function.prod f g ∘ h = Function.prod (f ∘ h) (g ∘ h) := rfl

/--
theorem `prod_comp_fst_comp_snd` / 定理 `prod_comp_fst_comp_snd`

English:
theorem prod_comp_fst_comp_snd
  given: {α₁ α₂ β₁ β₂} (f : α₁ -> α₂) (g : β₁ -> β₂)
  proof: rfl

中文:
定理 prod_comp_fst_comp_snd
  条件: {α₁ α₂ β₁ β₂} (f : α₁ -> α₂) (g : β₁ -> β₂)
  证明: rfl
-/
@[simp] theorem prod_comp_fst_comp_snd {α₁ α₂ β₁ β₂} (f : α₁ -> α₂) (g : β₁ -> β₂) :
    Function.prod (f ∘ Prod.fst) (g ∘ Prod.snd) = Prod.map f g := rfl

/--
theorem `map_comp_prod` / 定理 `map_comp_prod`

English:
theorem map_comp_prod
  given: {γ δ} (h : α -> γ) (k : β -> δ)
  proof: rfl

中文:
定理 map_comp_prod
  条件: {γ δ} (h : α -> γ) (k : β -> δ)
  证明: rfl
-/
@[simp] theorem map_comp_prod {γ δ} (h : α -> γ) (k : β -> δ) :
    Prod.map h k ∘ Function.prod f g = Function.prod (h ∘ f) (k ∘ g) := rfl

/--
theorem `prod_comp_prod` / 定理 `prod_comp_prod`

English:
theorem prod_comp_prod
  given: {γ δ} (h : α × β -> γ) (k : α × β -> δ)
  proof: rfl

中文:
定理 prod_comp_prod
  条件: {γ δ} (h : α × β -> γ) (k : α × β -> δ)
  证明: rfl
-/
theorem prod_comp_prod {γ δ} (h : α × β -> γ) (k : α × β -> δ) :
    Function.prod h k ∘ Function.prod f g =
      Function.prod (h ∘ Function.prod f g) (k ∘ Function.prod f g) := rfl

/--
theorem `swap_comp_prod` / 定理 `swap_comp_prod`

English:
theorem swap_comp_prod
  statement: Prod.swap ∘ Function.prod f g = Function.prod g f
  proof: rfl

中文:
定理 swap_comp_prod
  结论: Prod.swap ∘ Function.prod f g = Function.prod g f
  证明: rfl
-/
@[simp] theorem swap_comp_prod : Prod.swap ∘ Function.prod f g = Function.prod g f := rfl

end Prod

/- ### The diagonal map -/

/--
Definition of `diag` / `diag` 的定义

English:
definition diag
  signature: {α}
  body: fun a : α => (a, a)

中文:
定义 diag
  签名: {α}
  定义体: fun a : α => (a, a)
-/
@[inline] protected def diag {α} : α -> α × α := fun a : α => (a, a)

section Diag

variable {α β γ : Type*} (f : α -> β) (g : α -> γ) (a b : α)

/--
theorem `diag_def` / 定理 `diag_def`

English:
theorem diag_def
  statement: Function.diag = fun a : α => (a, a)
  proof: rfl

中文:
定理 diag_def
  结论: Function.diag = fun a : α => (a, a)
  证明: rfl
-/
theorem diag_def : Function.diag = fun a : α => (a, a) := rfl

/--
theorem `diag_apply` / 定理 `diag_apply`

English:
theorem diag_apply
  statement: Function.diag a = (a, a)
  proof: rfl

中文:
定理 diag_apply
  结论: Function.diag a = (a, a)
  证明: rfl
-/
@[simp, grind =] theorem diag_apply : Function.diag a = (a, a) := rfl

/--
theorem `diag_injective` / 定理 `diag_injective`

English:
theorem diag_injective
  statement: Injective (α := α) Function.diag
  proof: fun _ _ => congrArg Prod.fst

中文:
定理 diag_injective
  结论: Injective (α := α) Function.diag
  证明: fun _ _ => congrArg Prod.fst

Depends on / 依赖: Function, Function.diag, Prod.fst
-/
theorem diag_injective : Injective (α := α) Function.diag := fun _ _ => congrArg Prod.fst

/--
theorem `prod_id_id` / 定理 `prod_id_id`

English:
theorem prod_id_id
  statement: Function.prod (@id α) id = Function.diag
  proof: rfl

中文:
定理 prod_id_id
  结论: Function.prod (@id α) id = Function.diag
  证明: rfl
-/
@[simp] theorem prod_id_id : Function.prod (@id α) id = Function.diag := rfl
/--
theorem `fst_comp_diag` / 定理 `fst_comp_diag`

English:
theorem fst_comp_diag
  statement: Prod.fst ∘ Function.diag = @id α
  proof: rfl

中文:
定理 fst_comp_diag
  结论: Prod.fst ∘ Function.diag = @id α
  证明: rfl

Depends on / 依赖: Finset, Finset.smul_sum, ofModule, smul_sum
-/
@[simp] theorem fst_comp_diag : Prod.fst ∘ Function.diag = @id α := rfl
/--
theorem `snd_comp_diag` / 定理 `snd_comp_diag`

English:
theorem snd_comp_diag
  statement: Prod.snd ∘ Function.diag = @id α
  proof: rfl

中文:
定理 snd_comp_diag
  结论: Prod.snd ∘ Function.diag = @id α
  证明: rfl
-/
@[simp] theorem snd_comp_diag : Prod.snd ∘ Function.diag = @id α := rfl

/--
theorem `diag_comp` / 定理 `diag_comp`

English:
theorem diag_comp
  statement: Function.diag ∘ f = Function.prod f f
  proof: rfl

中文:
定理 diag_comp
  结论: Function.diag ∘ f = Function.prod f f
  证明: rfl

Depends on / 依赖: one_smul
-/
@[simp] theorem diag_comp : Function.diag ∘ f = Function.prod f f := rfl

/--
theorem `map_comp_diag` / 定理 `map_comp_diag`

English:
theorem map_comp_diag
  statement: Prod.map f g ∘ Function.diag = Function.prod f g
  proof: rfl

中文:
定理 map_comp_diag
  结论: Prod.map f g ∘ Function.diag = Function.prod f g
  证明: rfl
-/
@[simp] theorem map_comp_diag : Prod.map f g ∘ Function.diag = Function.prod f g := rfl

/--
theorem `swap_comp_diag` / 定理 `swap_comp_diag`

English:
theorem swap_comp_diag
  statement: Prod.swap ∘ Function.diag = Function.diag (α := α)
  proof: rfl

中文:
定理 swap_comp_diag
  结论: Prod.swap ∘ Function.diag = Function.diag (α := α)
  证明: rfl
-/
@[simp] theorem swap_comp_diag : Prod.swap ∘ Function.diag = Function.diag (α := α) := rfl

end Diag

/- ### `onFun` function -/

/--
Definition of `onFun` / `onFun` 的定义

English:
abbreviation onFun
  signature: (f : β -> β -> φ) (g : α -> β)
  body: fun x y => f (g x) (g y)

@[inherit_doc onFun]
scoped infixl:2 " on " => onFun

中文:
缩写 onFun
  签名: (f : β -> β -> φ) (g : α -> β)
  定义体: fun x y => f (g x) (g y)

@[inherit_doc onFun]
scoped infixl:2 " on " => onFun
-/
abbrev onFun (f : β -> β -> φ) (g : α -> β) : α -> α -> φ := fun x y => f (g x) (g y)

@[inherit_doc onFun]
scoped infixl:2 " on " => onFun

/- ### The argument-reversing map -/

/--
Definition of `swap` / `swap` 的定义

English:
abbreviation swap
  signature: {φ : α -> β -> Sort u₃} (f : forall x y, φ x y)
  body: fun y x => f x y

中文:
缩写 swap
  签名: {φ : α -> β -> Sort u₃} (f : 对任意 x y, φ x y)
  定义体: fun y x => f x y
-/
abbrev swap {φ : α -> β -> Sort u₃} (f : forall x y, φ x y) : forall y x, φ x y := fun y x => f x y

/--
theorem `swap_def` / 定理 `swap_def`

English:
theorem swap_def
  given: {φ : α -> β -> Sort u₃} (f : forall x y, φ x y)
  statement: swap f = fun y x => f x y
  proof: rfl

中文:
定理 swap_def
  条件: {φ : α -> β -> Sort u₃} (f : 对任意 x y, φ x y)
  结论: swap f = fun y x => f x y
  证明: rfl
-/
theorem swap_def {φ : α -> β -> Sort u₃} (f : forall x y, φ x y) : swap f = fun y x => f x y := rfl

/--
theorem `onFun_swap_comm` / 定理 `onFun_swap_comm`

English:
theorem onFun_swap_comm
  given: (f : β -> β -> φ) (g : α -> β)
  statement: (swap f on g) = swap (f on g)
  proof: rfl

中文:
定理 onFun_swap_comm
  条件: (f : β -> β -> φ) (g : α -> β)
  结论: (swap f on g) = swap (f on g)
  证明: rfl
-/
theorem onFun_swap_comm (f : β -> β -> φ) (g : α -> β) : (swap f on g) = swap (f on g) := rfl

/- ### Bijective functions -/

/--
Definition of `Bijective` / `Bijective` 的定义

English:
definition Bijective
  signature: (f : α -> β)
  body: Injective f ∧ Surjective f

中文:
定义 Bijective
  签名: (f : α -> β)
  定义体: Injective f ∧ Surjective f

Depends on / 依赖: Injective, Surjective
-/
def Bijective (f : α -> β) :=
  Injective f ∧ Surjective f

/--
theorem `Bijective.comp` / 定理 `Bijective.comp`

English:
theorem Bijective.comp
  given: {g : β -> φ} {f : α -> β}
  statement: Bijective g -> Bijective f -> Bijective (g ∘ f)

中文:
定理 Bijective.comp
  条件: {g : β -> φ} {f : α -> β}
  结论: Bijective g -> Bijective f -> Bijective (g ∘ f)
-/
theorem Bijective.comp {g : β -> φ} {f : α -> β} : Bijective g -> Bijective f -> Bijective (g ∘ f)
  | ⟨h_ginj, h_gsurj⟩, ⟨h_finj, h_fsurj⟩ => ⟨h_ginj.comp h_finj, h_gsurj.comp h_fsurj⟩

/--
theorem `bijective_id` / 定理 `bijective_id`

English:
theorem bijective_id
  statement: Bijective (@id α)
  proof: ⟨injective_id, surjective_id⟩

中文:
定理 bijective_id
  结论: Bijective (@id α)
  证明: ⟨injective_id, surjective_id⟩

Depends on / 依赖: injective_id, surjective_id
-/
theorem bijective_id : Bijective (@id α) :=
  ⟨injective_id, surjective_id⟩

variable {f : α -> β}

/--
theorem `Injective.beq_eq` / 定理 `Injective.beq_eq`

English:
theorem Injective.beq_eq
  statement: {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α -> β}
  proof: by
  by_cases h : a == b <;> simp [h] <;> simpa [I.eq_iff] using h

中文:
定理 Injective.beq_eq
  结论: {α β : 类型} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α -> β}
  证明: by
  by_cases h : a == b <;> simp [h] <;> simpa [I.eq_iff] using h

Depends on / 依赖: I.eq_iff, eq_iff
-/
theorem Injective.beq_eq {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α -> β}
    (I : Injective f) {a b : α} : (f a == f b) = (a == b) := by
  by_cases h : a == b <;> simp [h] <;> simpa [I.eq_iff] using h

/- ### Bicomposition -/

section Bicomp

variable {α β γ δ ε : Sort*}

/--
Definition of `bicompl` / `bicompl` 的定义

English:
definition bicompl
  signature: (f : γ -> δ -> ε) (g : α -> γ) (h : β -> δ) (a b)
  body: f (g a) (h b)

中文:
定义 bicompl
  签名: (f : γ -> δ -> ε) (g : α -> γ) (h : β -> δ) (a b)
  定义体: f (g a) (h b)
-/
def bicompl (f : γ -> δ -> ε) (g : α -> γ) (h : β -> δ) (a b) :=
  f (g a) (h b)

/--
Definition of `bicompr` / `bicompr` 的定义

English:
definition bicompr
  signature: (f : γ -> δ) (g : α -> β -> γ) (a b)
  body: f (g a b)

中文:
定义 bicompr
  签名: (f : γ -> δ) (g : α -> β -> γ) (a b)
  定义体: f (g a b)
-/
def bicompr (f : γ -> δ) (g : α -> β -> γ) (a b) :=
  f (g a b)

-- Suggested local notation:
local notation f " ∘₂ " g => bicompr f g

/--
theorem `uncurry_bicompr` / 定理 `uncurry_bicompr`

English:
theorem uncurry_bicompr
  given: {α β γ δ} (f : α -> β -> γ) (g : γ -> δ)
  statement: uncurry (g ∘₂ f) = g ∘ uncurry f
  proof: rfl

中文:
定理 uncurry_bicompr
  条件: {α β γ δ} (f : α -> β -> γ) (g : γ -> δ)
  结论: uncurry (g ∘₂ f) = g ∘ uncurry f
  证明: rfl
-/
theorem uncurry_bicompr {α β γ δ} (f : α -> β -> γ) (g : γ -> δ) : uncurry (g ∘₂ f) = g ∘ uncurry f :=
  rfl

/--
theorem `uncurry_bicompl` / 定理 `uncurry_bicompl`

English:
theorem uncurry_bicompl
  given: {α β γ δ ε} (f : γ -> δ -> ε) (g : α -> γ) (h : β -> δ)
  proof: rfl

中文:
定理 uncurry_bicompl
  条件: {α β γ δ ε} (f : γ -> δ -> ε) (g : α -> γ) (h : β -> δ)
  证明: rfl
-/
theorem uncurry_bicompl {α β γ δ ε} (f : γ -> δ -> ε) (g : α -> γ) (h : β -> δ) :
    uncurry (bicompl f g h) = uncurry f ∘ Prod.map g h :=
  rfl

end Bicomp

end Function

namespace Function

variable {α : Type u₁} {β : Type u₂}

/- ### Fixed points of functions -/

/--
Definition of `IsFixedPt` / `IsFixedPt` 的定义

English:
definition IsFixedPt
  signature: (f : α -> α) (x : α)
  body: f x = x

中文:
定义 IsFixedPt
  签名: (f : α -> α) (x : α)
  定义体: f x = x
-/
def IsFixedPt (f : α -> α) (x : α) := f x = x

/--
theorem `IsFixedPt.eq` / 定理 `IsFixedPt.eq`

English:
theorem IsFixedPt.eq
  given: {f : α -> α} {x : α} (hf : IsFixedPt f x)
  statement: f x = x
  proof: hf

中文:
定理 IsFixedPt.eq
  条件: {f : α -> α} {x : α} (hf : IsFixedPt f x)
  结论: f x = x
  证明: hf
-/
protected theorem IsFixedPt.eq {f : α -> α} {x : α} (hf : IsFixedPt f x) : f x = x :=
  hf

/--
Instance `IsFixedPt.decidable` / 实例 `IsFixedPt.decidable`

English:
instance IsFixedPt.decidable
  signature: [h : DecidableEq α] {f : α -> α} {x : α}
  body: h (f x) x

@[nontriviality]

中文:
实例 IsFixedPt.decidable
  签名: [h : DecidableEq α] {f : α -> α} {x : α}
  定义体: h (f x) x

@[nontriviality]
-/
instance IsFixedPt.decidable [h : DecidableEq α] {f : α -> α} {x : α} : Decidable (IsFixedPt f x) :=
  h (f x) x

@[nontriviality]
/--
theorem `IsFixedPt.of_subsingleton` / 定理 `IsFixedPt.of_subsingleton`

English:
theorem IsFixedPt.of_subsingleton
  given: [Subsingleton α] (f : α -> α) (x : α)
  statement: IsFixedPt f x
  proof: Subsingleton.elim _ _

中文:
定理 IsFixedPt.of_subsingleton
  条件: [Subsingleton α] (f : α -> α) (x : α)
  结论: IsFixedPt f x
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem IsFixedPt.of_subsingleton [Subsingleton α] (f : α -> α) (x : α) : IsFixedPt f x :=
  Subsingleton.elim _ _

/--
theorem `isFixedPt_id` / 定理 `isFixedPt_id`

English:
theorem isFixedPt_id
  given: (x : α)
  statement: IsFixedPt id x
  proof: rfl

中文:
定理 isFixedPt_id
  条件: (x : α)
  结论: IsFixedPt id x
  证明: rfl
-/
theorem isFixedPt_id (x : α) : IsFixedPt id x :=
  rfl

/--
theorem `forall_isFixedPt_iff` / 定理 `forall_isFixedPt_iff`

English:
theorem forall_isFixedPt_iff
  given: {f : α -> α}
  statement: (forall x, IsFixedPt f x) ↔ f = id
  proof: ⟨funext, fun h => h ▸ isFixedPt_id⟩

中文:
定理 forall_isFixedPt_iff
  条件: {f : α -> α}
  结论: (对任意 x, IsFixedPt f x) ↔ f = id
  证明: ⟨funext, fun h => h ▸ isFixedPt_id⟩
-/
@[simp] theorem forall_isFixedPt_iff {f : α -> α} : (forall x, IsFixedPt f x) ↔ f = id :=
  ⟨funext, fun h => h ▸ isFixedPt_id⟩

end Function

namespace Pi

variable {ι : Sort*} {α β : ι -> Sort*}

/- ### `Pi.map` function -/

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : forall i, α i -> β i)
  body: fun a i => f i (a i)

@[simp]

中文:
定义 map
  签名: (f : 对任意 i, α i -> β i)
  定义体: fun a i => f i (a i)

@[simp]
-/
protected def map (f : forall i, α i -> β i) : (forall i, α i) -> (forall i, β i) := fun a i => f i (a i)

@[simp]
/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  given: (f : forall i, α i -> β i) (a : forall i, α i) (i : ι)
  statement: Pi.map f a i = f i (a i)
  proof: rfl

中文:
引理 map_apply
  条件: (f : 对任意 i, α i -> β i) (a : 对任意 i, α i) (i : ι)
  结论: Pi.map f a i = f i (a i)
  证明: rfl
-/
lemma map_apply (f : forall i, α i -> β i) (a : forall i, α i) (i : ι) : Pi.map f a i = f i (a i) := rfl

end Pi
