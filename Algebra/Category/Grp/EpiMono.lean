/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Monomorphisms and epimorphisms in `Group`

In this file, we prove monomorphisms in the category of groups are injective homomorphisms and
epimorphisms are surjective homomorphisms.
-/

@[expose] public section


noncomputable section

open scoped Pointwise

universe u v

namespace MonoidHom

open QuotientGroup

variable {A : Type u} {B : Type v}

section

variable [Group A] [Group B]

@[to_additive]
/--
theorem `ker_eq_bot_of_cancel` / 定理 `ker_eq_bot_of_cancel`

English:
theorem ker_eq_bot_of_cancel
  given: {f : A ->* B} (h : forall u v : f.ker ->* A, f.comp u = f.comp v -> u = v)
  proof: by simpa using congr_arg range (h f.ker.subtype 1 (by cat_disch))

中文:
定理 ker_eq_bot_of_cancel
  条件: {f : A ->* B} (h : 对任意 u v : f.ker ->* A, f.comp u = f.comp v -> u = v)
  证明: by simpa using congr_arg range (h f.ker.subtype 1 (by cat_disch))

Depends on / 依赖: cat_disch, congr_arg, f.ker.subtype, subtype
-/
theorem ker_eq_bot_of_cancel {f : A ->* B} (h : forall u v : f.ker ->* A, f.comp u = f.comp v -> u = v) :
    f.ker = ⊥ := by simpa using congr_arg range (h f.ker.subtype 1 (by cat_disch))

end

section

variable [CommGroup A] [CommGroup B]

@[to_additive]
/--
theorem `range_eq_top_of_cancel` / 定理 `range_eq_top_of_cancel`

English:
theorem range_eq_top_of_cancel
  statement: {f : A ->* B}
  proof: by
  specialize h 1 (QuotientGroup.mk' _) _
  · ext1 x
    simp only [one_apply, coe_comp, coe_mk', Function.comp_apply]
    rw [show (1 : B ⧸ f.range) = (1 : B) from QuotientGroup.mk_one _]; rw [QuotientGroup.eq]; rw [inv_one]; rw [one_mul]
    exact ⟨x, rfl⟩
  replace h : (QuotientGroup.mk' f.rang

中文:
定理 range_eq_top_of_cancel
  结论: {f : A ->* B}
  证明: by
  specialize h 1 (QuotientGroup.mk' _) _
  · ext1 x
    simp only [one_apply, coe_comp, coe_mk', Function.comp_apply]
    rw [show (1 : B ⧸ f.range) = (1 : B) from QuotientGroup.mk_one _]; rw [QuotientGroup.eq]; rw [inv_one]; rw [one_mul]
    exact ⟨x, rfl⟩
  replace h : (QuotientGroup.mk' f.rang

Depends on / 依赖: Function, Function.comp_apply, QuotientGroup, QuotientGroup.eq, QuotientGroup.ker_mk, QuotientGroup.mk, QuotientGroup.mk_one, coe_comp, coe_mk, comp_apply, f.range, inv_one, ker_mk, ker_one, mk_one, one_apply, one_mul, replace, specialize
-/
theorem range_eq_top_of_cancel {f : A ->* B}
    (h : forall u v : B ->* B ⧸ f.range, u.comp f = v.comp f -> u = v) : f.range = ⊤ := by
  specialize h 1 (QuotientGroup.mk' _) _
  · ext1 x
    simp only [one_apply, coe_comp, coe_mk', Function.comp_apply]
    rw [show (1 : B ⧸ f.range) = (1 : B) from QuotientGroup.mk_one _]; rw [QuotientGroup.eq]; rw [inv_one]; rw [one_mul]
    exact ⟨x, rfl⟩
  replace h : (QuotientGroup.mk' f.range).ker = (1 : B ->* B ⧸ f.range).ker := by rw [h]
  rwa [ker_one, QuotientGroup.ker_mk'] at h

end

end MonoidHom

section

open CategoryTheory

namespace GrpCat

variable {A B : GrpCat.{u}} (f : A ⟶ B)

@[to_additive]
/--
theorem `ker_eq_bot_of_mono` / 定理 `ker_eq_bot_of_mono`

English:
theorem ker_eq_bot_of_mono
  given: [Mono f]
  statement: f.hom.ker = ⊥
  proof: MonoidHom.ker_eq_bot_of_cancel fun u v h => ConcreteCategory.ext_iff.mp
(@cancel_mono _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 ConcreteCategory.ext h

@[to_additive]

中文:
定理 ker_eq_bot_of_mono
  条件: [Mono f]
  结论: f.hom.ker = ⊥
  证明: MonoidHom.ker_eq_bot_of_cancel fun u v h => ConcreteCategory.ext_iff.mp
(@cancel_mono _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 ConcreteCategory.ext h

@[to_additive]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ext, ConcreteCategory.ext_iff.mp, MonoidHom, MonoidHom.ker_eq_bot_of_cancel, cancel_mono, ext_iff, ker_eq_bot_of_cancel
-/
theorem ker_eq_bot_of_mono [Mono f] : f.hom.ker = ⊥ :=
MonoidHom.ker_eq_bot_of_cancel fun u v h => ConcreteCategory.ext_iff.mp
(@cancel_mono _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 ConcreteCategory.ext h

@[to_additive]
/--
theorem `mono_iff_ker_eq_bot` / 定理 `mono_iff_ker_eq_bot`

English:
theorem mono_iff_ker_eq_bot
  statement: Mono f ↔ f.hom.ker = ⊥
  proof: ⟨fun _ => ker_eq_bot_of_mono f, fun h =>
ConcreteCategory.mono_of_injective _ (MonoidHom.ker_eq_bot_iff f.hom).1 h⟩

@[to_additive]

中文:
定理 mono_iff_ker_eq_bot
  结论: Mono f ↔ f.hom.ker = ⊥
  证明: ⟨fun _ => ker_eq_bot_of_mono f, fun h =>
ConcreteCategory.mono_of_injective _ (MonoidHom.ker_eq_bot_iff f.hom).1 h⟩

@[to_additive]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_of_injective, MonoidHom, MonoidHom.ker_eq_bot_iff, f.hom, ker_eq_bot_iff, ker_eq_bot_of_mono, mono_of_injective
-/
theorem mono_iff_ker_eq_bot : Mono f ↔ f.hom.ker = ⊥ :=
  ⟨fun _ => ker_eq_bot_of_mono f, fun h =>
ConcreteCategory.mono_of_injective _ (MonoidHom.ker_eq_bot_iff f.hom).1 h⟩

@[to_additive]
/--
theorem `mono_iff_injective` / 定理 `mono_iff_injective`

English:
theorem mono_iff_injective
  statement: Mono f ↔ Function.Injective f
  proof: Iff.trans (mono_iff_ker_eq_bot f) MonoidHom.ker_eq_bot_iff f.hom

中文:
定理 mono_iff_injective
  结论: Mono f ↔ Function.Injective f
  证明: Iff.trans (mono_iff_ker_eq_bot f) MonoidHom.ker_eq_bot_iff f.hom

Depends on / 依赖: Iff.trans, MonoidHom, MonoidHom.ker_eq_bot_iff, f.hom, ker_eq_bot_iff, mono_iff_ker_eq_bot
-/
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
Iff.trans (mono_iff_ker_eq_bot f) MonoidHom.ker_eq_bot_iff f.hom

namespace SurjectiveOfEpiAuxs

local notation3 "X" => Set.range (· • (f.hom.range : Set B) : B -> Set B)

/--
Inductive type `XWithInfinity` / 归纳类型 `XWithInfinity`

English:
inductive XWithInfinity
  constructors (2):
    - fromCoset: X -> XWithInfinity
    - infinity: XWithInfinity

中文:
归纳类型 XWithInfinity
  构造子 (2 个):
    - fromCoset: X -> XWithInfinity
    - infinity: XWithInfinity
-/
inductive XWithInfinity
  | fromCoset : X -> XWithInfinity
  | infinity : XWithInfinity

open XWithInfinity Equiv.Perm

local notation "X'" => XWithInfinity f

local notation "∞" => XWithInfinity.infinity

local notation "SX'" => Equiv.Perm X'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul B X'
  body: match x with
    | fromCoset y => fromCoset ⟨b • y, by
          rw [← y.2.choose_spec]; rw [leftCoset_assoc]
          let b' : B := y.2.choose
          use b * b'⟩
    | ∞ => ∞

中文:
实例 :
  签名: SMul B X'
  定义体: match x with
    | fromCoset y => fromCoset ⟨b • y, by
          rw [← y.2.choose_spec]; rw [leftCoset_assoc]
          let b' : B := y.2.choose
          use b * b'⟩
    | ∞ => ∞

Depends on / 依赖: choose_spec, fromCoset, leftCoset_assoc
-/
instance : SMul B X' where
  smul b x :=
    match x with
    | fromCoset y => fromCoset ⟨b • y, by
          rw [← y.2.choose_spec]; rw [leftCoset_assoc]
          let b' : B := y.2.choose
          use b * b'⟩
    | ∞ => ∞

/--
theorem `mul_smul` / 定理 `mul_smul`

English:
theorem mul_smul
  given: (b b' : B) (x : X')
  statement: (b * b') • x = b • b' • x
  proof: match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [leftCoset_assoc]
  | ∞ => rfl

中文:
定理 mul_smul
  条件: (b b' : B) (x : X')
  结论: (b * b') • x = b • b' • x
  证明: match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [leftCoset_assoc]
  | ∞ => rfl

Depends on / 依赖: fromCoset, leftCoset_assoc
-/
theorem mul_smul (b b' : B) (x : X') : (b * b') • x = b • b' • x :=
  match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [leftCoset_assoc]
  | ∞ => rfl

/--
theorem `one_smul` / 定理 `one_smul`

English:
theorem one_smul
  given: (x : X')
  statement: (1 : B) • x = x
  proof: match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [one_leftCoset]
  | ∞ => rfl

中文:
定理 one_smul
  条件: (x : X')
  结论: (1 : B) • x = x
  证明: match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [one_leftCoset]
  | ∞ => rfl

Depends on / 依赖: fromCoset, one_leftCoset
-/
theorem one_smul (x : X') : (1 : B) • x = x :=
  match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [one_leftCoset]
  | ∞ => rfl

/--
theorem `fromCoset_eq_of_mem_range` / 定理 `fromCoset_eq_of_mem_range`

English:
theorem fromCoset_eq_of_mem_range
  given: {b : B} (hb : b in f.hom.range)
  proof: by
  congr
  nth_rw 2 [show (f.hom.range : Set B) = (1 : B) • f.hom.range from (one_leftCoset _).symm]
  rw [leftCoset_eq_iff]; rw [mul_one]
  exact Subgroup.inv_mem _ hb

example (G : Type) [Group G] (S : Subgroup G) : Set G := S

中文:
定理 fromCoset_eq_of_mem_range
  条件: {b : B} (hb : b in f.hom.range)
  证明: by
  congr
  nth_rw 2 [show (f.hom.range : Set B) = (1 : B) • f.hom.range from (one_leftCoset _).symm]
  rw [leftCoset_eq_iff]; rw [mul_one]
  exact Subgroup.inv_mem _ hb

example (G : Type) [Group G] (S : Subgroup G) : Set G := S

Depends on / 依赖: Subgroup, Subgroup.inv_mem, f.hom.range, inv_mem, leftCoset_eq_iff, mul_one, nth_rw, one_leftCoset
-/
theorem fromCoset_eq_of_mem_range {b : B} (hb : b in f.hom.range) :
    fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  congr
  nth_rw 2 [show (f.hom.range : Set B) = (1 : B) • f.hom.range from (one_leftCoset _).symm]
  rw [leftCoset_eq_iff]; rw [mul_one]
  exact Subgroup.inv_mem _ hb

example (G : Type) [Group G] (S : Subgroup G) : Set G := S

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `fromCoset_ne_of_nin_range` / 定理 `fromCoset_ne_of_nin_range`

English:
theorem fromCoset_ne_of_nin_range
  given: {b : B} (hb : b ∉ f.hom.range)
  proof: by
  intro r
  simp only [fromCoset.injEq, Subtype.mk.injEq] at r
  nth_rw 2 [show (f.hom.range : Set B) = (1 : B) • f.hom.range from (one_leftCoset _).symm] at r
  rw [leftCoset_eq_iff]; rw [mul_one] at r
  exact hb (inv_inv b ▸ Subgroup.inv_mem _ r)

中文:
定理 fromCoset_ne_of_nin_range
  条件: {b : B} (hb : b ∉ f.hom.range)
  证明: by
  intro r
  simp only [fromCoset.injEq, Subtype.mk.injEq] at r
  nth_rw 2 [show (f.hom.range : Set B) = (1 : B) • f.hom.range from (one_leftCoset _).symm] at r
  rw [leftCoset_eq_iff]; rw [mul_one] at r
  exact hb (inv_inv b ▸ Subgroup.inv_mem _ r)

Depends on / 依赖: Subgroup, Subgroup.inv_mem, Subtype, Subtype.mk.injEq, f.hom.range, fromCoset, fromCoset.injEq, inv_inv, inv_mem, leftCoset_eq_iff, mul_one, nth_rw, one_leftCoset
-/
theorem fromCoset_ne_of_nin_range {b : B} (hb : b ∉ f.hom.range) :
    fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ != fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  intro r
  simp only [fromCoset.injEq, Subtype.mk.injEq] at r
  nth_rw 2 [show (f.hom.range : Set B) = (1 : B) • f.hom.range from (one_leftCoset _).symm] at r
  rw [leftCoset_eq_iff]; rw [mul_one] at r
  exact hb (inv_inv b ▸ Subgroup.inv_mem _ r)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableEq X'
  body: Classical.decEq _

中文:
实例 :
  签名: DecidableEq X'
  定义体: Classical.decEq _

Depends on / 依赖: Classical, Classical.decEq
-/
instance : DecidableEq X' :=
  Classical.decEq _

/--
Definition of `tau` / `tau` 的定义

English:
definition tau
  signature: : SX'
  body: Equiv.swap (fromCoset ⟨↑f.hom.range, ⟨1, one_leftCoset _⟩⟩) ∞

local notation "τ" => tau f

中文:
定义 tau
  签名: : SX'
  定义体: Equiv.swap (fromCoset ⟨↑f.hom.range, ⟨1, one_leftCoset _⟩⟩) ∞

local notation "τ" => tau f

Depends on / 依赖: Equiv.swap, f.hom.range, fromCoset, one_leftCoset
-/
noncomputable def tau : SX' :=
  Equiv.swap (fromCoset ⟨↑f.hom.range, ⟨1, one_leftCoset _⟩⟩) ∞

local notation "τ" => tau f

/--
theorem `τ_apply_infinity` / 定理 `τ_apply_infinity`

English:
theorem τ_apply_infinity
  statement: τ ∞ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩
  proof: Equiv.swap_apply_right _ _

中文:
定理 τ_apply_infinity
  结论: τ ∞ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩
  证明: Equiv.swap_apply_right _ _

Depends on / 依赖: Equiv.swap_apply_right, swap_apply_right
-/
theorem τ_apply_infinity : τ ∞ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ :=
  Equiv.swap_apply_right _ _

/--
theorem `τ_apply_fromCoset` / 定理 `τ_apply_fromCoset`

English:
theorem τ_apply_fromCoset
  statement: τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞
  proof: Equiv.swap_apply_left _ _

中文:
定理 τ_apply_fromCoset
  结论: τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞
  证明: Equiv.swap_apply_left _ _

Depends on / 依赖: Equiv.swap_apply_left, swap_apply_left
-/
theorem τ_apply_fromCoset : τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞ :=
  Equiv.swap_apply_left _ _

/--
theorem `τ_apply_fromCoset'` / 定理 `τ_apply_fromCoset'`

English:
theorem τ_apply_fromCoset'
  given: (x : B) (hx : x in f.hom.range)
  proof: (fromCoset_eq_of_mem_range _ hx).symm ▸ τ_apply_fromCoset _

中文:
定理 τ_apply_fromCoset'
  条件: (x : B) (hx : x in f.hom.range)
  证明: (fromCoset_eq_of_mem_range _ hx).symm ▸ τ_apply_fromCoset _

Depends on / 依赖: fromCoset_eq_of_mem_range
-/
theorem τ_apply_fromCoset' (x : B) (hx : x in f.hom.range) :
    τ (fromCoset ⟨x • ↑f.hom.range, ⟨x, rfl⟩⟩) = ∞ :=
  (fromCoset_eq_of_mem_range _ hx).symm ▸ τ_apply_fromCoset _

/--
theorem `τ_symm_apply_fromCoset` / 定理 `τ_symm_apply_fromCoset`

English:
theorem τ_symm_apply_fromCoset
  proof: by
  rw [tau]; rw [Equiv.symm_swap]; rw [Equiv.swap_apply_left]

中文:
定理 τ_symm_apply_fromCoset
  证明: by
  rw [tau]; rw [Equiv.symm_swap]; rw [Equiv.swap_apply_left]

Depends on / 依赖: Equiv.swap_apply_left, Equiv.symm_swap, swap_apply_left, symm_swap
-/
theorem τ_symm_apply_fromCoset :
    Equiv.symm τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞ := by
  rw [tau]; rw [Equiv.symm_swap]; rw [Equiv.swap_apply_left]

/--
theorem `τ_symm_apply_infinity` / 定理 `τ_symm_apply_infinity`

English:
theorem τ_symm_apply_infinity
  proof: by
  rw [tau]; rw [Equiv.symm_swap]; rw [Equiv.swap_apply_right]

中文:
定理 τ_symm_apply_infinity
  证明: by
  rw [tau]; rw [Equiv.symm_swap]; rw [Equiv.swap_apply_right]

Depends on / 依赖: Equiv.swap_apply_right, Equiv.symm_swap, swap_apply_right, symm_swap
-/
theorem τ_symm_apply_infinity :
    Equiv.symm τ ∞ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  rw [tau]; rw [Equiv.symm_swap]; rw [Equiv.swap_apply_right]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `g` / `g` 的定义

English:
definition g
  signature: : B ->* SX' where
  body: { toFun := fun x => β • x
      invFun := fun x => β⁻¹ • x
      left_inv := fun x => by
        dsimp only
        rw [← mul_smul]; rw [inv_mul_cancel]; rw [one_smul]
      right_inv := fun x => by
        dsimp only
        rw [← mul_smul]; rw [mul_inv_cancel]; rw [one_smul] }
  map_one' := by
   

中文:
定义 g
  签名: : B ->* SX' where
  定义体: { toFun := fun x => β • x
      invFun := fun x => β⁻¹ • x
      left_inv := fun x => by
        dsimp only
        rw [← mul_smul]; rw [inv_mul_cancel]; rw [one_smul]
      right_inv := fun x => by
        dsimp only
        rw [← mul_smul]; rw [mul_inv_cancel]; rw [one_smul] }
  map_one' := by
   

Depends on / 依赖: invFun, inv_mul_cancel, left_inv, map_mul, map_one, mul_inv_cancel, mul_smul, one_smul, right_inv
-/
def g : B ->* SX' where
  toFun β :=
    { toFun := fun x => β • x
      invFun := fun x => β⁻¹ • x
      left_inv := fun x => by
        dsimp only
        rw [← mul_smul]; rw [inv_mul_cancel]; rw [one_smul]
      right_inv := fun x => by
        dsimp only
        rw [← mul_smul]; rw [mul_inv_cancel]; rw [one_smul] }
  map_one' := by
    ext
    simp [one_smul]
  map_mul' b1 b2 := by
    ext
    simp [mul_smul]

local notation "g" => g f

/--
Definition of `h` / `h` 的定义

English:
definition h
  signature: : B ->* SX' where
  body: ((τ).symm.trans (g β)).trans τ
  map_one' := by
    ext
    simp
  map_mul' b1 b2 := by
    ext
    simp

local notation "h" => h f

中文:
定义 h
  签名: : B ->* SX' where
  定义体: ((τ).symm.trans (g β)).trans τ
  map_one' := by
    ext
    simp
  map_mul' b1 b2 := by
    ext
    simp

local notation "h" => h f

Depends on / 依赖: symm.trans
-/
def h : B ->* SX' where
  toFun β := ((τ).symm.trans (g β)).trans τ
  map_one' := by
    ext
    simp
  map_mul' b1 b2 := by
    ext
    simp

local notation "h" => h f



/--
theorem `g_apply_fromCoset` / 定理 `g_apply_fromCoset`

English:
theorem g_apply_fromCoset
  given: (x : B) (y : X)
  proof: y.2; exact ⟨x * z, by simp [← hz, smul_smul]⟩⟩ := rfl

中文:
定理 g_apply_fromCoset
  条件: (x : B) (y : X)
  证明: y.2; exact ⟨x * z, by simp [← hz, smul_smul]⟩⟩ := rfl

Depends on / 依赖: smul_smul
-/
theorem g_apply_fromCoset (x : B) (y : X) :
    g x (fromCoset y) = fromCoset ⟨x • ↑y,
      by obtain ⟨z, hz⟩ := y.2; exact ⟨x * z, by simp [← hz, smul_smul]⟩⟩ := rfl

/--
theorem `g_apply_infinity` / 定理 `g_apply_infinity`

English:
theorem g_apply_infinity
  given: (x : B)
  statement: (g x) ∞ = ∞
  proof: rfl

中文:
定理 g_apply_infinity
  条件: (x : B)
  结论: (g x) ∞ = ∞
  证明: rfl
-/
theorem g_apply_infinity (x : B) : (g x) ∞ = ∞ := rfl

/--
theorem `h_apply_infinity` / 定理 `h_apply_infinity`

English:
theorem h_apply_infinity
  given: (x : B) (hx : x in f.hom.range)
  statement: (h x) ∞ = ∞
  proof: by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp only [Equiv.coe_trans, Function.comp_apply]
  rw [τ_symm_apply_infinity]; rw [g_apply_fromCoset]
  exact τ_apply_fromCoset' f x hx

中文:
定理 h_apply_infinity
  条件: (x : B) (hx : x in f.hom.range)
  结论: (h x) ∞ = ∞
  证明: by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp only [Equiv.coe_trans, Function.comp_apply]
  rw [τ_symm_apply_infinity]; rw [g_apply_fromCoset]
  exact τ_apply_fromCoset' f x hx

Depends on / 依赖: Equiv.coe_trans, Function, Function.comp_apply, coe_trans, comp_apply, g_apply_fromCoset, symm.trans
-/
theorem h_apply_infinity (x : B) (hx : x in f.hom.range) : (h x) ∞ = ∞ := by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp only [Equiv.coe_trans, Function.comp_apply]
  rw [τ_symm_apply_infinity]; rw [g_apply_fromCoset]
  exact τ_apply_fromCoset' f x hx

/--
theorem `h_apply_fromCoset` / 定理 `h_apply_fromCoset`

English:
theorem h_apply_fromCoset
  given: (x : B)
  proof: by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp [-MonoidHom.coe_range, τ_symm_apply_fromCoset, g_apply_infinity, τ_apply_infinity]

中文:
定理 h_apply_fromCoset
  条件: (x : B)
  证明: by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp [-MonoidHom.coe_range, τ_symm_apply_fromCoset, g_apply_infinity, τ_apply_infinity]

Depends on / 依赖: MonoidHom, MonoidHom.coe_range, coe_range, g_apply_infinity, symm.trans
-/
theorem h_apply_fromCoset (x : B) :
    (h x) (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) =
      fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp [-MonoidHom.coe_range, τ_symm_apply_fromCoset, g_apply_infinity, τ_apply_infinity]

/--
theorem `h_apply_fromCoset'` / 定理 `h_apply_fromCoset'`

English:
theorem h_apply_fromCoset'
  given: (x : B) (b : B) (hb : b in f.hom.range)
  proof: (fromCoset_eq_of_mem_range _ hb).symm ▸ h_apply_fromCoset f x

中文:
定理 h_apply_fromCoset'
  条件: (x : B) (b : B) (hb : b in f.hom.range)
  证明: (fromCoset_eq_of_mem_range _ hb).symm ▸ h_apply_fromCoset f x

Depends on / 依赖: fromCoset_eq_of_mem_range, h_apply_fromCoset
-/
theorem h_apply_fromCoset' (x : B) (b : B) (hb : b in f.hom.range) :
    h x (fromCoset ⟨b • f.hom.range, b, rfl⟩) = fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ :=
  (fromCoset_eq_of_mem_range _ hb).symm ▸ h_apply_fromCoset f x

/--
theorem `h_apply_fromCoset_nin_range` / 定理 `h_apply_fromCoset_nin_range`

English:
theorem h_apply_fromCoset_nin_range
  given: (x : B) (hx : x in f.hom.range) (b : B) (hb : b ∉ f.hom.range)
  proof: by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp only [tau, Equiv.coe_trans, Function.comp_apply]
  rw [Equiv.symm_swap]; rw [@Equiv.swap_apply_of_ne_of_ne X' _ (fromCoset ⟨f.hom.range]; rw [1]; rw [one_leftCoset _⟩) ∞
      (fromCoset ⟨b • ↑f.hom.range]; rw [b]; rw [rfl⟩) (fromCoset_ne_of_ni

中文:
定理 h_apply_fromCoset_nin_range
  条件: (x : B) (hx : x in f.hom.range) (b : B) (hb : b ∉ f.hom.range)
  证明: by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp only [tau, Equiv.coe_trans, Function.comp_apply]
  rw [Equiv.symm_swap]; rw [@Equiv.swap_apply_of_ne_of_ne X' _ (fromCoset ⟨f.hom.range]; rw [1]; rw [one_leftCoset _⟩) ∞
      (fromCoset ⟨b • ↑f.hom.range]; rw [b]; rw [rfl⟩) (fromCoset_ne_of_ni

Depends on / 依赖: Equiv.coe_trans, Equiv.swap_apply_of_ne_of_ne, Equiv.symm_swap, Function, Function.comp_apply, Subgroup, Subgroup.inv_mem, Subgroup.mul_mem, coe_trans, comp_apply, convert, f.hom.range, fromCoset, fromCoset_ne_of_nin_range, g_apply_fromCoset, inv_mem, leftCoset_assoc, mul_mem, one_leftCoset, swap_apply_of_ne_of_ne
-/
theorem h_apply_fromCoset_nin_range (x : B) (hx : x in f.hom.range) (b : B) (hb : b ∉ f.hom.range) :
    h x (fromCoset ⟨b • f.hom.range, b, rfl⟩) = fromCoset ⟨(x * b) • ↑f.hom.range, x * b, rfl⟩ := by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp only [tau, Equiv.coe_trans, Function.comp_apply]
  rw [Equiv.symm_swap]; rw [@Equiv.swap_apply_of_ne_of_ne X' _ (fromCoset ⟨f.hom.range]; rw [1]; rw [one_leftCoset _⟩) ∞
      (fromCoset ⟨b • ↑f.hom.range]; rw [b]; rw [rfl⟩) (fromCoset_ne_of_nin_range _ hb) (by simp)]
  simp only [g_apply_fromCoset, leftCoset_assoc]
  refine Equiv.swap_apply_of_ne_of_ne (fromCoset_ne_of_nin_range _ fun r => hb ?_) (by simp)
  convert! Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) r
  rw [← mul_assoc]; rw [inv_mul_cancel]; rw [one_mul]

/--
theorem `agree` / 定理 `agree`

English:
theorem agree
  statement: f.hom.range = { x | h x = g x }
  proof: by
  refine Set.ext fun b => ⟨?_, fun hb : h b = g b => by_contradiction fun r => ?_⟩
  · rintro ⟨a, rfl⟩
    change h (f a) = g (f a)
    ext ⟨⟨_, ⟨y, rfl⟩⟩⟩
    · rw [g_apply_fromCoset]
      by_cases m : y in f.hom.range
      · rw [h_apply_fromCoset' _ _ _ m, fromCoset_eq_of_mem_range _ m]
     

中文:
定理 agree
  结论: f.hom.range = { x | h x = g x }
  证明: by
  refine Set.ext fun b => ⟨?_, fun hb : h b = g b => by_contradiction fun r => ?_⟩
  · rintro ⟨a, rfl⟩
    change h (f a) = g (f a)
    ext ⟨⟨_, ⟨y, rfl⟩⟩⟩
    · rw [g_apply_fromCoset]
      by_cases m : y in f.hom.range
      · rw [h_apply_fromCoset' _ _ _ m, fromCoset_eq_of_mem_range _ m]
     

Depends on / 依赖: Set.ext, Subgroup, Subgroup.mul_mem, by_contradiction, f.hom.range, fromCoset, fromCoset_eq_of_mem_range, g_apply_, g_apply_fromCoset, h_apply_fromCoset, h_apply_fromCoset_nin_range, leftCoset_assoc, mul_mem, smul_smul
-/
theorem agree : f.hom.range = { x | h x = g x } := by
  refine Set.ext fun b => ⟨?_, fun hb : h b = g b => by_contradiction fun r => ?_⟩
  · rintro ⟨a, rfl⟩
    change h (f a) = g (f a)
    ext ⟨⟨_, ⟨y, rfl⟩⟩⟩
    · rw [g_apply_fromCoset]
      by_cases m : y in f.hom.range
      · rw [h_apply_fromCoset' _ _ _ m, fromCoset_eq_of_mem_range _ m]
        change fromCoset _ = fromCoset ⟨f a • (y • _), _⟩
        simp only [← fromCoset_eq_of_mem_range _ (Subgroup.mul_mem _ ⟨a, rfl⟩ m), smul_smul]
      · rw [h_apply_fromCoset_nin_range f (f a) ⟨_, rfl⟩ _ m]
        simp only [leftCoset_assoc]
    · rw [g_apply_infinity, h_apply_infinity f (f a) ⟨_, rfl⟩]
  · have eq1 : (h b) (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) =
        fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
      change ((τ).symm.trans (g b)).trans τ _ = _
      dsimp [tau]
      simp [g_apply_infinity f]
    have eq2 :
        g b (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ :=
      rfl
    exact (fromCoset_ne_of_nin_range _ r).symm (by rw [← eq1, ← eq2, DFunLike.congr_fun hb])

/--
theorem `comp_eq` / 定理 `comp_eq`

English:
theorem comp_eq
  statement: (f ≫ ofHom g) = f ≫ ofHom h
  proof: by
  ext a
  simp only [hom_comp, hom_ofHom, MonoidHom.coe_comp, Function.comp_apply]
  have : f a in { b | h b = g b } := by
    rw [← agree]
    use a
  rw [this]

中文:
定理 comp_eq
  结论: (f ≫ ofHom g) = f ≫ ofHom h
  证明: by
  ext a
  simp only [hom_comp, hom_ofHom, MonoidHom.coe_comp, Function.comp_apply]
  have : f a in { b | h b = g b } := by
    rw [← agree]
    use a
  rw [this]

Depends on / 依赖: Function, Function.comp_apply, MonoidHom, MonoidHom.coe_comp, coe_comp, comp_apply, hom_comp, hom_ofHom
-/
theorem comp_eq : (f ≫ ofHom g) = f ≫ ofHom h := by
  ext a
  simp only [hom_comp, hom_ofHom, MonoidHom.coe_comp, Function.comp_apply]
  have : f a in { b | h b = g b } := by
    rw [← agree]
    use a
  rw [this]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `g_ne_h` / 定理 `g_ne_h`

English:
theorem g_ne_h
  given: (x : B) (hx : x ∉ f.hom.range)
  statement: g != h
  proof: by
  intro r
  apply fromCoset_ne_of_nin_range _ hx
  replace r :=
    DFunLike.congr_fun (DFunLike.congr_fun r x) (fromCoset ⟨f.hom.range, ⟨1, one_leftCoset _⟩⟩)
  simpa [g_apply_fromCoset, «h», tau, g_apply_infinity] using r

中文:
定理 g_ne_h
  条件: (x : B) (hx : x ∉ f.hom.range)
  结论: g != h
  证明: by
  intro r
  apply fromCoset_ne_of_nin_range _ hx
  replace r :=
    DFunLike.congr_fun (DFunLike.congr_fun r x) (fromCoset ⟨f.hom.range, ⟨1, one_leftCoset _⟩⟩)
  simpa [g_apply_fromCoset, «h», tau, g_apply_infinity] using r

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, f.hom.range, fromCoset, fromCoset_ne_of_nin_range, g_apply_fromCoset, g_apply_infinity, one_leftCoset, replace
-/
theorem g_ne_h (x : B) (hx : x ∉ f.hom.range) : g != h := by
  intro r
  apply fromCoset_ne_of_nin_range _ hx
  replace r :=
    DFunLike.congr_fun (DFunLike.congr_fun r x) (fromCoset ⟨f.hom.range, ⟨1, one_leftCoset _⟩⟩)
  simpa [g_apply_fromCoset, «h», tau, g_apply_infinity] using r

end SurjectiveOfEpiAuxs

/--
theorem `surjective_of_epi` / 定理 `surjective_of_epi`

English:
theorem surjective_of_epi
  given: [Epi f]
  statement: Function.Surjective f
  proof: by
  dsimp [Function.Surjective]
  by_contra! ⟨b, hb⟩
  exact
    SurjectiveOfEpiAuxs.g_ne_h f b (fun ⟨c, hc⟩ => hb _ hc)
      (congr_arg GrpCat.Hom.hom ((cancel_epi f).1 (SurjectiveOfEpiAuxs.comp_eq f)))

中文:
定理 surjective_of_epi
  条件: [Epi f]
  结论: Function.Surjective f
  证明: by
  dsimp [Function.Surjective]
  by_contra! ⟨b, hb⟩
  exact
    SurjectiveOfEpiAuxs.g_ne_h f b (fun ⟨c, hc⟩ => hb _ hc)
      (congr_arg GrpCat.Hom.hom ((cancel_epi f).1 (SurjectiveOfEpiAuxs.comp_eq f)))

Depends on / 依赖: Function, Function.Surjective, GrpCat, GrpCat.Hom.hom, Surjective, SurjectiveOfEpiAuxs, SurjectiveOfEpiAuxs.comp_eq, SurjectiveOfEpiAuxs.g_ne_h, cancel_epi, comp_eq, congr_arg, g_ne_h
-/
theorem surjective_of_epi [Epi f] : Function.Surjective f := by
  dsimp [Function.Surjective]
  by_contra! ⟨b, hb⟩
  exact
    SurjectiveOfEpiAuxs.g_ne_h f b (fun ⟨c, hc⟩ => hb _ hc)
      (congr_arg GrpCat.Hom.hom ((cancel_epi f).1 (SurjectiveOfEpiAuxs.comp_eq f)))

/--
theorem `epi_iff_surjective` / 定理 `epi_iff_surjective`

English:
theorem epi_iff_surjective
  statement: Epi f ↔ Function.Surjective f
  proof: ⟨fun _ => surjective_of_epi f, ConcreteCategory.epi_of_surjective f⟩

中文:
定理 epi_iff_surjective
  结论: Epi f ↔ Function.Surjective f
  证明: ⟨fun _ => surjective_of_epi f, ConcreteCategory.epi_of_surjective f⟩

Depends on / 依赖: ConcreteCategory, ConcreteCategory.epi_of_surjective, epi_of_surjective, surjective_of_epi
-/
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f :=
  ⟨fun _ => surjective_of_epi f, ConcreteCategory.epi_of_surjective f⟩

/--
theorem `epi_iff_range_eq_top` / 定理 `epi_iff_range_eq_top`

English:
theorem epi_iff_range_eq_top
  statement: Epi f ↔ f.hom.range = ⊤
  proof: Iff.trans (epi_iff_surjective _) (Subgroup.eq_top_iff' f.hom.range).symm

中文:
定理 epi_iff_range_eq_top
  结论: Epi f ↔ f.hom.range = ⊤
  证明: Iff.trans (epi_iff_surjective _) (Subgroup.eq_top_iff' f.hom.range).symm

Depends on / 依赖: Iff.trans, Subgroup, Subgroup.eq_top_iff, epi_iff_surjective, eq_top_iff, f.hom.range
-/
theorem epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (Subgroup.eq_top_iff' f.hom.range).symm

end GrpCat

namespace AddGrpCat


variable {A B : AddGrpCat.{u}} (f : A ⟶ B)

/--
theorem `epi_iff_surjective` / 定理 `epi_iff_surjective`

English:
theorem epi_iff_surjective
  statement: Epi f ↔ Function.Surjective f
  proof: by
  have i1 : Epi f ↔ Epi (groupAddGroupEquivalence.inverse.map f) := by
    refine ⟨?_, groupAddGroupEquivalence.inverse.epi_of_epi_map⟩
    apply groupAddGroupEquivalence.inverse.map_epi
  rwa [GrpCat.epi_iff_surjective] at i1

中文:
定理 epi_iff_surjective
  结论: Epi f ↔ Function.Surjective f
  证明: by
  have i1 : Epi f ↔ Epi (groupAddGroupEquivalence.inverse.map f) := by
    refine ⟨?_, groupAddGroupEquivalence.inverse.epi_of_epi_map⟩
    apply groupAddGroupEquivalence.inverse.map_epi
  rwa [GrpCat.epi_iff_surjective] at i1

Depends on / 依赖: GrpCat, GrpCat.epi_iff_surjective, epi_iff_surjective, epi_of_epi_map, groupAddGroupEquivalence, groupAddGroupEquivalence.inverse.epi_of_epi_map, groupAddGroupEquivalence.inverse.map, groupAddGroupEquivalence.inverse.map_epi, inverse, map_epi
-/
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  have i1 : Epi f ↔ Epi (groupAddGroupEquivalence.inverse.map f) := by
    refine ⟨?_, groupAddGroupEquivalence.inverse.epi_of_epi_map⟩
    apply groupAddGroupEquivalence.inverse.map_epi
  rwa [GrpCat.epi_iff_surjective] at i1

/--
theorem `epi_iff_range_eq_top` / 定理 `epi_iff_range_eq_top`

English:
theorem epi_iff_range_eq_top
  statement: Epi f ↔ f.hom.range = ⊤
  proof: Iff.trans (epi_iff_surjective _) (AddSubgroup.eq_top_iff' f.hom.range).symm

中文:
定理 epi_iff_range_eq_top
  结论: Epi f ↔ f.hom.range = ⊤
  证明: Iff.trans (epi_iff_surjective _) (AddSubgroup.eq_top_iff' f.hom.range).symm

Depends on / 依赖: AddSubgroup, AddSubgroup.eq_top_iff, Iff.trans, epi_iff_surjective, eq_top_iff, f.hom.range
-/
theorem epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (AddSubgroup.eq_top_iff' f.hom.range).symm

end AddGrpCat

namespace GrpCat


variable {A B : GrpCat.{u}} (f : A ⟶ B)

@[to_additive AddGrpCat.forget_grp_preserves_mono]
/--
Instance `forget_grp_preserves_mono` / 实例 `forget_grp_preserves_mono`

English:
instance forget_grp_preserves_mono
  signature: : (forget GrpCat).PreservesMonomorphisms where
  body: by rwa [mono_iff_injective, ← CategoryTheory.ofHom_mono_iff_injective] at e

@[to_additive AddGrpCat.forget_grp_preserves_epi]

中文:
实例 forget_grp_preserves_mono
  签名: : (forget GrpCat).PreservesMonomorphisms where
  定义体: by rwa [mono_iff_injective, ← CategoryTheory.ofHom_mono_iff_injective] at e

@[to_additive AddGrpCat.forget_grp_preserves_epi]

Depends on / 依赖: CategoryTheory, CategoryTheory.ofHom_mono_iff_injective, mono_iff_injective, ofHom_mono_iff_injective
-/
instance forget_grp_preserves_mono : (forget GrpCat).PreservesMonomorphisms where
  preserves f e := by rwa [mono_iff_injective, ← CategoryTheory.ofHom_mono_iff_injective] at e

@[to_additive AddGrpCat.forget_grp_preserves_epi]
/--
Instance `forget_grp_preserves_epi` / 实例 `forget_grp_preserves_epi`

English:
instance forget_grp_preserves_epi
  signature: : (forget GrpCat).PreservesEpimorphisms where
  body: by rwa [epi_iff_surjective, ← CategoryTheory.ofHom_epi_iff_surjective] at e

中文:
实例 forget_grp_preserves_epi
  签名: : (forget GrpCat).PreservesEpimorphisms where
  定义体: by rwa [epi_iff_surjective, ← CategoryTheory.ofHom_epi_iff_surjective] at e

Depends on / 依赖: CategoryTheory, CategoryTheory.ofHom_epi_iff_surjective, epi_iff_surjective, ofHom_epi_iff_surjective
-/
instance forget_grp_preserves_epi : (forget GrpCat).PreservesEpimorphisms where
  preserves f e := by rwa [epi_iff_surjective, ← CategoryTheory.ofHom_epi_iff_surjective] at e

end GrpCat

namespace CommGrpCat


variable {A B : CommGrpCat.{u}} (f : A ⟶ B)

@[to_additive]
/--
theorem `ker_eq_bot_of_mono` / 定理 `ker_eq_bot_of_mono`

English:
theorem ker_eq_bot_of_mono
  given: [Mono f]
  statement: f.hom.ker = ⊥
  proof: MonoidHom.ker_eq_bot_of_cancel fun u v h => ConcreteCategory.ext_iff.mp
(@cancel_mono _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 ConcreteCategory.ext h

@[to_additive]

中文:
定理 ker_eq_bot_of_mono
  条件: [Mono f]
  结论: f.hom.ker = ⊥
  证明: MonoidHom.ker_eq_bot_of_cancel fun u v h => ConcreteCategory.ext_iff.mp
(@cancel_mono _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 ConcreteCategory.ext h

@[to_additive]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ext, ConcreteCategory.ext_iff.mp, MonoidHom, MonoidHom.ker_eq_bot_of_cancel, cancel_mono, ext_iff, ker_eq_bot_of_cancel
-/
theorem ker_eq_bot_of_mono [Mono f] : f.hom.ker = ⊥ :=
MonoidHom.ker_eq_bot_of_cancel fun u v h => ConcreteCategory.ext_iff.mp
(@cancel_mono _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 ConcreteCategory.ext h

@[to_additive]
/--
theorem `mono_iff_ker_eq_bot` / 定理 `mono_iff_ker_eq_bot`

English:
theorem mono_iff_ker_eq_bot
  statement: Mono f ↔ f.hom.ker = ⊥
  proof: ⟨fun _ => ker_eq_bot_of_mono f, fun h =>
ConcreteCategory.mono_of_injective _ (MonoidHom.ker_eq_bot_iff f.hom).1 h⟩

@[to_additive]

中文:
定理 mono_iff_ker_eq_bot
  结论: Mono f ↔ f.hom.ker = ⊥
  证明: ⟨fun _ => ker_eq_bot_of_mono f, fun h =>
ConcreteCategory.mono_of_injective _ (MonoidHom.ker_eq_bot_iff f.hom).1 h⟩

@[to_additive]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_of_injective, MonoidHom, MonoidHom.ker_eq_bot_iff, f.hom, ker_eq_bot_iff, ker_eq_bot_of_mono, mono_of_injective
-/
theorem mono_iff_ker_eq_bot : Mono f ↔ f.hom.ker = ⊥ :=
  ⟨fun _ => ker_eq_bot_of_mono f, fun h =>
ConcreteCategory.mono_of_injective _ (MonoidHom.ker_eq_bot_iff f.hom).1 h⟩

@[to_additive]
/--
theorem `mono_iff_injective` / 定理 `mono_iff_injective`

English:
theorem mono_iff_injective
  statement: Mono f ↔ Function.Injective f
  proof: Iff.trans (mono_iff_ker_eq_bot f) MonoidHom.ker_eq_bot_iff f.hom

@[to_additive]

中文:
定理 mono_iff_injective
  结论: Mono f ↔ Function.Injective f
  证明: Iff.trans (mono_iff_ker_eq_bot f) MonoidHom.ker_eq_bot_iff f.hom

@[to_additive]

Depends on / 依赖: Iff.trans, MonoidHom, MonoidHom.ker_eq_bot_iff, f.hom, ker_eq_bot_iff, mono_iff_ker_eq_bot
-/
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
Iff.trans (mono_iff_ker_eq_bot f) MonoidHom.ker_eq_bot_iff f.hom

@[to_additive]
/--
theorem `range_eq_top_of_epi` / 定理 `range_eq_top_of_epi`

English:
theorem range_eq_top_of_epi
  given: [Epi f]
  statement: f.hom.range = ⊤
  proof: MonoidHom.range_eq_top_of_cancel fun u v h => ConcreteCategory.ext_iff.mp
    (@cancel_epi _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 (ConcreteCategory.ext h)

@[to_additive]

中文:
定理 range_eq_top_of_epi
  条件: [Epi f]
  结论: f.hom.range = ⊤
  证明: MonoidHom.range_eq_top_of_cancel fun u v h => ConcreteCategory.ext_iff.mp
    (@cancel_epi _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 (ConcreteCategory.ext h)

@[to_additive]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ext, ConcreteCategory.ext_iff.mp, MonoidHom, MonoidHom.range_eq_top_of_cancel, cancel_epi, ext_iff, range_eq_top_of_cancel
-/
theorem range_eq_top_of_epi [Epi f] : f.hom.range = ⊤ :=
MonoidHom.range_eq_top_of_cancel fun u v h => ConcreteCategory.ext_iff.mp
    (@cancel_epi _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 (ConcreteCategory.ext h)

@[to_additive]
/--
theorem `epi_iff_range_eq_top` / 定理 `epi_iff_range_eq_top`

English:
theorem epi_iff_range_eq_top
  statement: Epi f ↔ f.hom.range = ⊤
  proof: ⟨fun _ => range_eq_top_of_epi _, fun hf =>
ConcreteCategory.epi_of_surjective _ show Function.Surjective f.hom from
      MonoidHom.range_eq_top.mp hf⟩

@[to_additive]

中文:
定理 epi_iff_range_eq_top
  结论: Epi f ↔ f.hom.range = ⊤
  证明: ⟨fun _ => range_eq_top_of_epi _, fun hf =>
ConcreteCategory.epi_of_surjective _ show Function.Surjective f.hom from
      MonoidHom.range_eq_top.mp hf⟩

@[to_additive]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.epi_of_surjective, Function, Function.Surjective, MonoidHom, MonoidHom.range_eq_top.mp, Surjective, epi_of_surjective, f.hom, range_eq_top, range_eq_top_of_epi
-/
theorem epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤ :=
  ⟨fun _ => range_eq_top_of_epi _, fun hf =>
ConcreteCategory.epi_of_surjective _ show Function.Surjective f.hom from
      MonoidHom.range_eq_top.mp hf⟩

@[to_additive]
/--
theorem `epi_iff_surjective` / 定理 `epi_iff_surjective`

English:
theorem epi_iff_surjective
  statement: Epi f ↔ Function.Surjective f
  proof: by
  rw [epi_iff_range_eq_top]; rw [MonoidHom.range_eq_top]

@[to_additive AddCommGrpCat.forget_commGrp_preserves_mono]

中文:
定理 epi_iff_surjective
  结论: Epi f ↔ Function.Surjective f
  证明: by
  rw [epi_iff_range_eq_top]; rw [MonoidHom.range_eq_top]

@[to_additive AddCommGrpCat.forget_commGrp_preserves_mono]

Depends on / 依赖: MonoidHom, MonoidHom.range_eq_top, epi_iff_range_eq_top, range_eq_top
-/
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top]; rw [MonoidHom.range_eq_top]

@[to_additive AddCommGrpCat.forget_commGrp_preserves_mono]
/--
Instance `forget_commGrp_preserves_mono` / 实例 `forget_commGrp_preserves_mono`

English:
instance forget_commGrp_preserves_mono
  signature: : (forget CommGrpCat).PreservesMonomorphisms where
  body: by rwa [mono_iff_injective, ← CategoryTheory.ofHom_mono_iff_injective] at e

@[to_additive AddCommGrpCat.forget_commGrp_preserves_epi]

中文:
实例 forget_commGrp_preserves_mono
  签名: : (forget CommGrpCat).PreservesMonomorphisms where
  定义体: by rwa [mono_iff_injective, ← CategoryTheory.ofHom_mono_iff_injective] at e

@[to_additive AddCommGrpCat.forget_commGrp_preserves_epi]

Depends on / 依赖: CategoryTheory, CategoryTheory.ofHom_mono_iff_injective, mono_iff_injective, ofHom_mono_iff_injective
-/
instance forget_commGrp_preserves_mono : (forget CommGrpCat).PreservesMonomorphisms where
  preserves f e := by rwa [mono_iff_injective, ← CategoryTheory.ofHom_mono_iff_injective] at e

@[to_additive AddCommGrpCat.forget_commGrp_preserves_epi]
/--
Instance `forget_commGrp_preserves_epi` / 实例 `forget_commGrp_preserves_epi`

English:
instance forget_commGrp_preserves_epi
  signature: : (forget CommGrpCat).PreservesEpimorphisms where
  body: by rwa [epi_iff_surjective, ← CategoryTheory.ofHom_epi_iff_surjective] at e

中文:
实例 forget_commGrp_preserves_epi
  签名: : (forget CommGrpCat).PreservesEpimorphisms where
  定义体: by rwa [epi_iff_surjective, ← CategoryTheory.ofHom_epi_iff_surjective] at e

Depends on / 依赖: CategoryTheory, CategoryTheory.ofHom_epi_iff_surjective, epi_iff_surjective, ofHom_epi_iff_surjective
-/
instance forget_commGrp_preserves_epi : (forget CommGrpCat).PreservesEpimorphisms where
  preserves f e := by rwa [epi_iff_surjective, ← CategoryTheory.ofHom_epi_iff_surjective] at e

end CommGrpCat

end
