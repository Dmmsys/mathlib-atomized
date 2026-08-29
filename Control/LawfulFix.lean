/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.Stream.Init
public import Mathlib.Control.Fix
public import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Lawful fixed point operators

This module defines the laws required of a `Fix` instance, using the theory of
omega complete partial orders (ωCPO). Proofs of the lawfulness of all `Fix` instances in
`Control.Fix` are provided.

## Main definition

* class `LawfulFix`
-/

@[expose] public section

universe u v

variable {α : Type*} {β : α -> Type*}

open OmegaCompletePartialOrder

/--
Definition of `LawfulFix` / `LawfulFix` 的定义

English:
class LawfulFix
  parameters: (α : Type*) [OmegaCompletePartialOrder α]
  extends: Fix α
  axioms and operations (1):
    - fix_eq : forall {f : α -> α}, ωScottContinuous f -> Fix.fix f = f (Fix.fix f)

中文:
类 LawfulFix
  参数: (α : 类型) [OmegaCompletePartial序 α]
  继承: Fix α
  公理与运算 (1 个):
    - fix_eq : 对任意 {f : α -> α}, ωScottContinuous f -> Fix.fix f = f (Fix.fix f)
-/
class LawfulFix (α : Type*) [OmegaCompletePartialOrder α] extends Fix α where
  fix_eq : forall {f : α -> α}, ωScottContinuous f -> Fix.fix f = f (Fix.fix f)

namespace Part

open Nat Nat.Upto

namespace Fix

variable (f : ((a : _) -> Part <| β a) ->o (a : _) -> Part <| β a)

/--
theorem `approx_mono'` / 定理 `approx_mono'`

English:
theorem approx_mono'
  given: {i : Nat}
  statement: Fix.approx f i <= Fix.approx f (succ i)
  proof: by
  induction i with
  | zero => dsimp [approx]; apply @bot_le _ _ _ (f ⊥)
  | succ _ i_ih => intro; apply f.monotone; apply i_ih

中文:
定理 approx_mono'
  条件: {i : 自然数}
  结论: Fix.approx f i <= Fix.approx f (succ i)
  证明: by
  induction i with
  | zero => dsimp [approx]; apply @bot_le _ _ _ (f ⊥)
  | succ _ i_ih => intro; apply f.monotone; apply i_ih

Depends on / 依赖: approx, bot_le, f.monotone, i_ih, monotone
-/
theorem approx_mono' {i : Nat} : Fix.approx f i <= Fix.approx f (succ i) := by
  induction i with
  | zero => dsimp [approx]; apply @bot_le _ _ _ (f ⊥)
  | succ _ i_ih => intro; apply f.monotone; apply i_ih

/--
theorem `approx_mono` / 定理 `approx_mono`

English:
theorem approx_mono
  given: ⦃i j
  statement: Nat⦄ (hij : i <= j) : approx f i <= approx f j
  proof: by
  induction j with
  | zero => cases hij; exact le_rfl
  | succ j ih =>
    cases hij; · exact le_rfl
    exact le_trans (ih ‹_›) (approx_mono' f)

中文:
定理 approx_mono
  条件: ⦃i j
  结论: 自然数⦄ (hij : i <= j) : approx f i <= approx f j
  证明: by
  induction j with
  | zero => cases hij; exact le_rfl
  | succ j ih =>
    cases hij; · exact le_rfl
    exact le_trans (ih ‹_›) (approx_mono' f)

Depends on / 依赖: approx_mono, le_rfl, le_trans
-/
theorem approx_mono ⦃i j : Nat⦄ (hij : i <= j) : approx f i <= approx f j := by
  induction j with
  | zero => cases hij; exact le_rfl
  | succ j ih =>
    cases hij; · exact le_rfl
    exact le_trans (ih ‹_›) (approx_mono' f)

/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: (a : α) (b : β a)
  statement: b in Part.fix f a ↔ exists i, b in approx f i a
  proof: by
  classical
  by_cases h₀ : exists i : Nat, (approx f i a).Dom
  · simp only [Part.fix_def f h₀]
    constructor <;> intro hh
    · exact ⟨_, hh⟩
    have h₁ := Nat.find_spec h₀
    rw [dom_iff_mem] at h₁
    obtain ⟨y, h₁⟩ := h₁
    replace h₁ := approx_mono' f _ _ h₁
    suffices y = b by
     

中文:
定理 mem_iff
  条件: (a : α) (b : β a)
  结论: b in Part.fix f a ↔ 存在 i, b in approx f i a
  证明: by
  classical
  by_cases h₀ : exists i : Nat, (approx f i a).Dom
  · simp only [Part.fix_def f h₀]
    constructor <;> intro hh
    · exact ⟨_, hh⟩
    have h₁ := Nat.find_spec h₀
    rw [dom_iff_mem] at h₁
    obtain ⟨y, h₁⟩ := h₁
    replace h₁ := approx_mono' f _ _ h₁
    suffices y = b by
     

Depends on / 依赖: Nat.find, Nat.find_spec, Part.fix_def, apply_assumption, approx, approx_mono, classical, dom_iff_mem, find_spec, fix_def, generalize, le_total, replace, revert
-/
theorem mem_iff (a : α) (b : β a) : b in Part.fix f a ↔ exists i, b in approx f i a := by
  classical
  by_cases h₀ : exists i : Nat, (approx f i a).Dom
  · simp only [Part.fix_def f h₀]
    constructor <;> intro hh
    · exact ⟨_, hh⟩
    have h₁ := Nat.find_spec h₀
    rw [dom_iff_mem] at h₁
    obtain ⟨y, h₁⟩ := h₁
    replace h₁ := approx_mono' f _ _ h₁
    suffices y = b by
      subst this
      exact h₁
    obtain ⟨i, hh⟩ := hh
    revert h₁; generalize succ (Nat.find h₀) = j; intro h₁
    wlog case : i <= j
    · rcases le_total i j with H | H <;> [skip; symm] <;> apply_assumption <;> assumption
    replace hh := approx_mono f case _ _ hh
    apply Part.mem_unique h₁ hh
  · simp only [fix_def' (⇑f) h₀, not_exists, false_iff, notMem_none]
    simp only [dom_iff_mem, not_exists] at h₀
    intro; apply h₀

/--
theorem `approx_le_fix` / 定理 `approx_le_fix`

English:
theorem approx_le_fix
  given: (i : Nat)
  statement: approx f i <= Part.fix f
  proof: fun a b hh => by
  rw [mem_iff f]
  exact ⟨_, hh⟩

中文:
定理 approx_le_fix
  条件: (i : 自然数)
  结论: approx f i <= Part.fix f
  证明: fun a b hh => by
  rw [mem_iff f]
  exact ⟨_, hh⟩

Depends on / 依赖: mem_iff
-/
theorem approx_le_fix (i : Nat) : approx f i <= Part.fix f := fun a b hh => by
  rw [mem_iff f]
  exact ⟨_, hh⟩

/--
theorem `exists_fix_le_approx` / 定理 `exists_fix_le_approx`

English:
theorem exists_fix_le_approx
  given: (x : α)
  statement: exists i, Part.fix f x <= approx f i x
  proof: by
  by_cases! hh : exists i b, b in approx f i x
  · rcases hh with ⟨i, b, hb⟩
    exists i
    intro b' h'
    have hb' := approx_le_fix f i _ _ hb
    obtain rfl := Part.mem_unique h' hb'
    exact hb
  · exists 0
    intro b' h'
    simp only [mem_iff f] at h'
    obtain ⟨i, h'⟩ := h'
    cases 

中文:
定理 存在_fix_le_approx
  条件: (x : α)
  结论: 存在 i, Part.fix f x <= approx f i x
  证明: by
  by_cases! hh : exists i b, b in approx f i x
  · rcases hh with ⟨i, b, hb⟩
    exists i
    intro b' h'
    have hb' := approx_le_fix f i _ _ hb
    obtain rfl := Part.mem_unique h' hb'
    exact hb
  · exists 0
    intro b' h'
    simp only [mem_iff f] at h'
    obtain ⟨i, h'⟩ := h'
    cases 

Depends on / 依赖: Part.mem_unique, approx, approx_le_fix, mem_iff, mem_unique
-/
theorem exists_fix_le_approx (x : α) : exists i, Part.fix f x <= approx f i x := by
  by_cases! hh : exists i b, b in approx f i x
  · rcases hh with ⟨i, b, hb⟩
    exists i
    intro b' h'
    have hb' := approx_le_fix f i _ _ hb
    obtain rfl := Part.mem_unique h' hb'
    exact hb
  · exists 0
    intro b' h'
    simp only [mem_iff f] at h'
    obtain ⟨i, h'⟩ := h'
    cases hh _ _ h'

/--
Definition of `approxChain` / `approxChain` 的定义

English:
definition approxChain
  signature: : Chain ((a : _) -> Part <| β a)
  body: ⟨approx f, approx_mono f⟩

中文:
定义 approxChain
  签名: : 链 ((a : _) -> Part <| β a)
  定义体: ⟨approx f, approx_mono f⟩

Depends on / 依赖: approx, approx_mono
-/
def approxChain : Chain ((a : _) -> Part <| β a) :=
  ⟨approx f, approx_mono f⟩

/--
theorem `le_f_of_mem_approx` / 定理 `le_f_of_mem_approx`

English:
theorem le_f_of_mem_approx
  given: {x}
  statement: x in approxChain f -> x <= f x
  proof: by
  simp only [Membership.mem, forall_exists_index]
  rintro i rfl
  apply approx_mono'

中文:
定理 le_f_of_mem_approx
  条件: {x}
  结论: x in approxChain f -> x <= f x
  证明: by
  simp only [Membership.mem, forall_exists_index]
  rintro i rfl
  apply approx_mono'

Depends on / 依赖: Membership, Membership.mem, approx_mono, forall_exists_index
-/
theorem le_f_of_mem_approx {x} : x in approxChain f -> x <= f x := by
  simp only [Membership.mem, forall_exists_index]
  rintro i rfl
  apply approx_mono'

/--
theorem `approx_mem_approxChain` / 定理 `approx_mem_approxChain`

English:
theorem approx_mem_approxChain
  given: {i}
  statement: approx f i in approxChain f
  proof: Stream'.mem_of_get_eq rfl

中文:
定理 approx_mem_approxChain
  条件: {i}
  结论: approx f i in approxChain f
  证明: Stream'.mem_of_get_eq rfl

Depends on / 依赖: Stream, mem_of_get_eq
-/
theorem approx_mem_approxChain {i} : approx f i in approxChain f :=
  Stream'.mem_of_get_eq rfl

end Fix

open Part.Fix

variable {α : Type*}
variable (f : ((a : _) -> Part <| β a) ->o (a : _) -> Part <| β a)

/--
theorem `fix_eq_ωSup` / 定理 `fix_eq_ωSup`

English:
theorem fix_eq_ωSup
  statement: Part.fix f = ωSup (approxChain f)
  proof: by
  apply le_antisymm
  · intro x
    obtain ⟨i, hx⟩ := exists_fix_le_approx f x
    trans approx f i.succ x
    · trans
      · apply hx
      · apply approx_mono' f
    apply le_ωSup_of_le i.succ
    dsimp [approx]
    rfl
  · apply ωSup_le _ _ _
    simp only [Fix.approxChain]
    intro y x
    

中文:
定理 fix_eq_ωSup
  结论: Part.fix f = ωSup (approxChain f)
  证明: by
  apply le_antisymm
  · intro x
    obtain ⟨i, hx⟩ := exists_fix_le_approx f x
    trans approx f i.succ x
    · trans
      · apply hx
      · apply approx_mono' f
    apply le_ωSup_of_le i.succ
    dsimp [approx]
    rfl
  · apply ωSup_le _ _ _
    simp only [Fix.approxChain]
    intro y x
    

Depends on / 依赖: Fix.approxChain, approx, approxChain, approx_le_fix, approx_mono, exists_fix_le_approx, i.succ, le_antisymm
-/
theorem fix_eq_ωSup : Part.fix f = ωSup (approxChain f) := by
  apply le_antisymm
  · intro x
    obtain ⟨i, hx⟩ := exists_fix_le_approx f x
    trans approx f i.succ x
    · trans
      · apply hx
      · apply approx_mono' f
    apply le_ωSup_of_le i.succ
    dsimp [approx]
    rfl
  · apply ωSup_le _ _ _
    simp only [Fix.approxChain]
    intro y x
    apply approx_le_fix f

/--
theorem `fix_le` / 定理 `fix_le`

English:
theorem fix_le
  given: {X : (a : _) -> Part <| β a} (hX : f X <= X)
  statement: Part.fix f <= X
  proof: by
  rw [fix_eq_ωSup f]
  apply ωSup_le _ _ _
  simp only [Fix.approxChain]
  intro i
  induction i with
  | zero => apply bot_le
  | succ _ i_ih =>
    trans f X
    · apply f.monotone i_ih
    · apply hX

中文:
定理 fix_le
  条件: {X : (a : _) -> Part <| β a} (hX : f X <= X)
  结论: Part.fix f <= X
  证明: by
  rw [fix_eq_ωSup f]
  apply ωSup_le _ _ _
  simp only [Fix.approxChain]
  intro i
  induction i with
  | zero => apply bot_le
  | succ _ i_ih =>
    trans f X
    · apply f.monotone i_ih
    · apply hX

Depends on / 依赖: Fix.approxChain, approxChain, bot_le, f.monotone, i_ih, monotone
-/
theorem fix_le {X : (a : _) -> Part <| β a} (hX : f X <= X) : Part.fix f <= X := by
  rw [fix_eq_ωSup f]
  apply ωSup_le _ _ _
  simp only [Fix.approxChain]
  intro i
  induction i with
  | zero => apply bot_le
  | succ _ i_ih =>
    trans f X
    · apply f.monotone i_ih
    · apply hX

variable {g : ((a : _) -> Part <| β a) -> (a : _) -> Part <| β a}

/--
theorem `fix_eq_ωSup_of_ωScottContinuous` / 定理 `fix_eq_ωSup_of_ωScottContinuous`

English:
theorem fix_eq_ωSup_of_ωScottContinuous
  given: (hc : ωScottContinuous g)
  statement: Part.fix g =
  proof: by
  rw [← fix_eq_ωSup]
  rfl

中文:
定理 fix_eq_ωSup_of_ωScottContinuous
  条件: (hc : ωScottContinuous g)
  结论: Part.fix g =
  证明: by
  rw [← fix_eq_ωSup]
  rfl
-/
theorem fix_eq_ωSup_of_ωScottContinuous (hc : ωScottContinuous g) : Part.fix g =
    ωSup (approxChain (⟨g,hc.monotone⟩ : ((a : _) -> Part <| β a) ->o (a : _) -> Part <| β a)) := by
  rw [← fix_eq_ωSup]
  rfl

/--
theorem `fix_eq_of_ωScottContinuous` / 定理 `fix_eq_of_ωScottContinuous`

English:
theorem fix_eq_of_ωScottContinuous
  given: (hc : ωScottContinuous g)
  proof: by
  rw [fix_eq_ωSup_of_ωScottContinuous hc]; rw [hc.map_ωSup]
  apply le_antisymm
  · apply ωSup_le_ωSup_of_le _
    intro i
    exists i
    apply le_f_of_mem_approx _ ⟨i, rfl⟩
  · apply ωSup_le_ωSup_of_le _
    intro i
    exists i.succ

中文:
定理 fix_eq_of_ωScottContinuous
  条件: (hc : ωScottContinuous g)
  证明: by
  rw [fix_eq_ωSup_of_ωScottContinuous hc]; rw [hc.map_ωSup]
  apply le_antisymm
  · apply ωSup_le_ωSup_of_le _
    intro i
    exists i
    apply le_f_of_mem_approx _ ⟨i, rfl⟩
  · apply ωSup_le_ωSup_of_le _
    intro i
    exists i.succ

Depends on / 依赖: hc.map_, i.succ, le_antisymm, le_f_of_mem_approx
-/
theorem fix_eq_of_ωScottContinuous (hc : ωScottContinuous g) :
    Part.fix g = g (Part.fix g) := by
  rw [fix_eq_ωSup_of_ωScottContinuous hc]; rw [hc.map_ωSup]
  apply le_antisymm
  · apply ωSup_le_ωSup_of_le _
    intro i
    exists i
    apply le_f_of_mem_approx _ ⟨i, rfl⟩
  · apply ωSup_le_ωSup_of_le _
    intro i
    exists i.succ

end Part

namespace Part

/-- `toUnit` as a monotone function -/
@[simps]
/--
Definition of `toUnitMono` / `toUnitMono` 的定义

English:
definition toUnitMono
  signature: (f : Part α ->o Part α)
  body: f (x u)
monotone' x y (h : x <= y) u := f.monotone h u

中文:
定义 toUnitMono
  签名: (f : Part α ->o Part α)
  定义体: f (x u)
monotone' x y (h : x <= y) u := f.monotone h u
-/
def toUnitMono (f : Part α ->o Part α) : (Unit -> Part α) ->o Unit -> Part α where
  toFun x u := f (x u)
monotone' x y (h : x <= y) u := f.monotone h u

set_option backward.defeqAttrib.useBackward true in
/--
theorem `ωScottContinuous_toUnitMono` / 定理 `ωScottContinuous_toUnitMono`

English:
theorem ωScottContinuous_toUnitMono
  given: (f : Part α -> Part α) (hc : ωScottContinuous f)
  proof: .of_map_ωSup_of_orderHom fun _ => by
  ext ⟨⟩ : 1
  dsimp [OmegaCompletePartialOrder.ωSup]
  erw [hc.map_ωSup]
  rw [Chain.map_comp]
  rfl

中文:
定理 ωScottContinuous_toUnitMono
  条件: (f : Part α -> Part α) (hc : ωScottContinuous f)
  证明: .of_map_ωSup_of_orderHom fun _ => by
  ext ⟨⟩ : 1
  dsimp [OmegaCompletePartialOrder.ωSup]
  erw [hc.map_ωSup]
  rw [Chain.map_comp]
  rfl

Depends on / 依赖: Chain.map_comp, OmegaCompletePartialOrder, hc.map_, map_comp
-/
theorem ωScottContinuous_toUnitMono (f : Part α -> Part α) (hc : ωScottContinuous f) :
    ωScottContinuous (toUnitMono ⟨f,hc.monotone⟩) := .of_map_ωSup_of_orderHom fun _ => by
  ext ⟨⟩ : 1
  dsimp [OmegaCompletePartialOrder.ωSup]
  erw [hc.map_ωSup]
  rw [Chain.map_comp]
  rfl

/--
Instance `lawfulFix` / 实例 `lawfulFix`

English:
instance lawfulFix
  signature: : LawfulFix (Part α)
  body: ⟨fun {f : Part α -> Part α} hc => show Part.fix (toUnitMono ⟨f,hc.monotone⟩) () = _ by
    rw [Part.fix_eq_of_ωScottContinuous (ωScottContinuous_toUnitMono f hc)]; rfl⟩

中文:
实例 lawfulFix
  签名: : LawfulFix (Part α)
  定义体: ⟨fun {f : Part α -> Part α} hc => show Part.fix (toUnitMono ⟨f,hc.monotone⟩) () = _ by
    rw [Part.fix_eq_of_ωScottContinuous (ωScottContinuous_toUnitMono f hc)]; rfl⟩

Depends on / 依赖: Part.fix, Part.fix_eq_of_, hc.monotone, monotone, toUnitMono
-/
noncomputable instance lawfulFix : LawfulFix (Part α) :=
  ⟨fun {f : Part α -> Part α} hc => show Part.fix (toUnitMono ⟨f,hc.monotone⟩) () = _ by
    rw [Part.fix_eq_of_ωScottContinuous (ωScottContinuous_toUnitMono f hc)]; rfl⟩

end Part

open Sigma

namespace Pi

/--
Instance `lawfulFix` / 实例 `lawfulFix`

English:
instance lawfulFix
  signature: {β}
  body: ⟨fun {_f} => Part.fix_eq_of_ωScottContinuous⟩

中文:
实例 lawfulFix
  签名: {β}
  定义体: ⟨fun {_f} => Part.fix_eq_of_ωScottContinuous⟩

Depends on / 依赖: Part.fix_eq_of_
-/
noncomputable instance lawfulFix {β} : LawfulFix (α -> Part β) :=
  ⟨fun {_f} => Part.fix_eq_of_ωScottContinuous⟩

variable {γ : forall a : α, β a -> Type*}

section Monotone

variable (α β γ)

/-- `Sigma.curry` as a monotone function. -/
@[simps]
/--
Definition of `monotoneCurry` / `monotoneCurry` 的定义

English:
definition monotoneCurry
  signature: [(x y : _) -> Preorder <| γ x y]
  body: curry
  monotone' _x _y h a b := h ⟨a, b⟩

中文:
定义 monotoneCurry
  签名: [(x y : _) -> 预序 <| γ x y]
  定义体: curry
  monotone' _x _y h a b := h ⟨a, b⟩
-/
def monotoneCurry [(x y : _) -> Preorder <| γ x y] :
    (forall x : Σ a, β a, γ x.1 x.2) ->o forall (a) (b : β a), γ a b where
  toFun := curry
  monotone' _x _y h a b := h ⟨a, b⟩

/-- `Sigma.uncurry` as a monotone function. -/
@[simps]
/--
Definition of `monotoneUncurry` / `monotoneUncurry` 的定义

English:
definition monotoneUncurry
  signature: [(x y : _) -> Preorder <| γ x y]
  body: uncurry
  monotone' _x _y h a := h a.1 a.2

中文:
定义 monotoneUncurry
  签名: [(x y : _) -> 预序 <| γ x y]
  定义体: uncurry
  monotone' _x _y h a := h a.1 a.2

Depends on / 依赖: uncurry
-/
def monotoneUncurry [(x y : _) -> Preorder <| γ x y] :
    (forall (a) (b : β a), γ a b) ->o forall x : Σ a, β a, γ x.1 x.2 where
  toFun := uncurry
  monotone' _x _y h a := h a.1 a.2

variable [(x y : _) -> OmegaCompletePartialOrder <| γ x y]

open OmegaCompletePartialOrder.Chain

/--
theorem `ωScottContinuous_curry` / 定理 `ωScottContinuous_curry`

English:
theorem ωScottContinuous_curry
  proof: ωScottContinuous.of_map_ωSup_of_orderHom fun c => by
    ext x y
    dsimp [curry, ωSup]
    rw [map_comp]; rw [map_comp]
    rfl

中文:
定理 ωScottContinuous_curry
  证明: ωScottContinuous.of_map_ωSup_of_orderHom fun c => by
    ext x y
    dsimp [curry, ωSup]
    rw [map_comp]; rw [map_comp]
    rfl

Depends on / 依赖: ScottContinuous.of_map_, map_comp
-/
theorem ωScottContinuous_curry :
    ωScottContinuous (monotoneCurry α β γ) :=
  ωScottContinuous.of_map_ωSup_of_orderHom fun c => by
    ext x y
    dsimp [curry, ωSup]
    rw [map_comp]; rw [map_comp]
    rfl

set_option backward.defeqAttrib.useBackward true in
/--
theorem `ωScottContinuous_uncurry` / 定理 `ωScottContinuous_uncurry`

English:
theorem ωScottContinuous_uncurry
  proof: .of_map_ωSup_of_orderHom fun c => by
  ext ⟨x, y⟩
  dsimp [uncurry, ωSup]
  rw [map_comp]; rw [map_comp]
  rfl

中文:
定理 ωScottContinuous_uncurry
  证明: .of_map_ωSup_of_orderHom fun c => by
  ext ⟨x, y⟩
  dsimp [uncurry, ωSup]
  rw [map_comp]; rw [map_comp]
  rfl

Depends on / 依赖: map_comp, uncurry
-/
theorem ωScottContinuous_uncurry :
    ωScottContinuous (monotoneUncurry α β γ) :=
    .of_map_ωSup_of_orderHom fun c => by
  ext ⟨x, y⟩
  dsimp [uncurry, ωSup]
  rw [map_comp]; rw [map_comp]
  rfl

end Monotone

open Fix

/--
Instance `hasFix` / 实例 `hasFix`

English:
instance hasFix
  signature: [Fix <| (x : Sigma β) -> γ x.1 x.2]
  body: ⟨fun f => curry (fix <| uncurry ∘ f ∘ curry)⟩

中文:
实例 hasFix
  签名: [Fix <| (x : 依赖和类型 β) -> γ x.1 x.2]
  定义体: ⟨fun f => curry (fix <| uncurry ∘ f ∘ curry)⟩

Depends on / 依赖: uncurry
-/
instance hasFix [Fix <| (x : Sigma β) -> γ x.1 x.2] : Fix ((x : _) -> (y : β x) -> γ x y) :=
  ⟨fun f => curry (fix <| uncurry ∘ f ∘ curry)⟩

variable [forall x y, OmegaCompletePartialOrder <| γ x y]

section Curry

variable {f : (forall a b, γ a b) -> forall a b, γ a b}

/--
theorem `uncurry_curry_ωScottContinuous` / 定理 `uncurry_curry_ωScottContinuous`

English:
theorem uncurry_curry_ωScottContinuous
  given: (hc : ωScottContinuous f)
  proof: (ωScottContinuous_uncurry _ _ _).comp (hc.comp (ωScottContinuous_curry _ _ _))

中文:
定理 uncurry_curry_ωScottContinuous
  条件: (hc : ωScottContinuous f)
  证明: (ωScottContinuous_uncurry _ _ _).comp (hc.comp (ωScottContinuous_curry _ _ _))

Depends on / 依赖: hc.comp
-/
theorem uncurry_curry_ωScottContinuous (hc : ωScottContinuous f) :
ωScottContinuous (monotoneUncurry α β γ).comp
(⟨f,hc.monotone⟩ : ((x : _) -> (y : β x) -> γ x y) ->o (x : _) -> (y : β x) -> γ x y).comp
      monotoneCurry α β γ :=
  (ωScottContinuous_uncurry _ _ _).comp (hc.comp (ωScottContinuous_curry _ _ _))

end Curry

/--
Instance `lawfulFix'` / 实例 `lawfulFix'`

English:
instance lawfulFix'
  signature: [LawfulFix <| (x : Sigma β) -> γ x.1 x.2]
  body: by
    dsimp [fix]
    conv_lhs => erw [LawfulFix.fix_eq (uncurry_curry_ωScottContinuous hc)]
    rfl

中文:
实例 lawfulFix'
  签名: [LawfulFix <| (x : 依赖和类型 β) -> γ x.1 x.2]
  定义体: by
    dsimp [fix]
    conv_lhs => erw [LawfulFix.fix_eq (uncurry_curry_ωScottContinuous hc)]
    rfl

Depends on / 依赖: LawfulFix, LawfulFix.fix_eq, conv_lhs, fix_eq
-/
instance lawfulFix' [LawfulFix <| (x : Sigma β) -> γ x.1 x.2] :
    LawfulFix ((x y : _) -> γ x y) where
  fix_eq {_f} hc := by
    dsimp [fix]
    conv_lhs => erw [LawfulFix.fix_eq (uncurry_curry_ωScottContinuous hc)]
    rfl

end Pi
