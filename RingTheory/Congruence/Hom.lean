/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.RingTheory.Congruence.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Congruence relations and ring homomorphisms

This file contains elementary definitions involving congruence
relations and morphisms for rings and semirings

## Main definitions

* `RingCon.ker`: the kernel of a monoid homomorphism as a congruence relation
* `RingCon.lift`, `RingCon.liftₐ`: the homomorphism / the algebra morphism
  on the quotient given that the congruence is in the kernel
* `RingCon.map`, `RingCon.mapₐ`: homomorphism / algebra morphism
  from a smaller to a larger quotient

* `RingCon.quotientKerEquivRangeS`, `RingCon.quotientKerEquivRange`,
  `RingCon.quotientKerEquivRangeₐ` :
  the first isomorphism theorem for semirings (using `RingHom.rangeS`),
  rings (using `RingHom.range`) and algebras (using `AlgHom.range`).
* `RingCon.comapQuotientEquivRangeS`, `RingCon.comapQuotientEquivRange`,
  `RingCon.comapQuotientEquivRangeₐ` : the second isomorphism theorem
  for semirings (using `RingHom.rangeS`), rings (using `RingHom.range`)
  and algebras (using `AlgHom.range`).

* `RingCon.quotientQuotientEquivQuotient`, `RingCon.quotientQuotientEquivQuotientₐ` :
  the third isomorphism theorem for semirings (or rings) and algebras

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, ring,
quotient ring
-/

@[expose] public section

variable {M : Type*} {N : Type*} {P : Type*}

open Function Setoid

namespace RingCon

section

variable [NonAssocSemiring M] [NonAssocSemiring N] [NonAssocSemiring P] {c d : RingCon M}

/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: (f : M ->+* N)
  body: comap ⊥ f

中文:
定义 ker
  签名: (f : M ->+* N)
  定义体: comap ⊥ f
-/
def ker (f : M ->+* N) : RingCon M := comap ⊥ f

/--
theorem `comap_bot` / 定理 `comap_bot`

English:
theorem comap_bot
  given: (f : M ->+* N)
  statement: comap ⊥ f = ker f
  proof: rfl

中文:
定理 comap_bot
  条件: (f : M ->+* N)
  结论: comap ⊥ f = ker f
  证明: rfl
-/
theorem comap_bot (f : M ->+* N) : comap ⊥ f = ker f := rfl

/-- The definition of the ring congruence relation defined by a ring homomorphism's kernel. -/
@[simp]
/--
theorem `ker_apply` / 定理 `ker_apply`

English:
theorem ker_apply
  given: (f : M ->+* N) {x y}
  statement: ker f x y ↔ f x = f y
  proof: Iff.rfl

中文:
定理 ker_apply
  条件: (f : M ->+* N) {x y}
  结论: ker f x y ↔ f x = f y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ker_apply (f : M ->+* N) {x y} : ker f x y ↔ f x = f y :=
  Iff.rfl

/--
theorem `ker_mk'_eq` / 定理 `ker_mk'_eq`

English:
theorem ker_mk'_eq
  given: (c : RingCon M)
  statement: ker c.mk' = c
  proof: ext fun _ _ => Quotient.eq''

中文:
定理 ker_mk'_eq
  条件: (c : RingCon M)
  结论: ker c.mk' = c
  证明: ext fun _ _ => Quotient.eq''

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem ker_mk'_eq (c : RingCon M) : ker c.mk' = c :=
  ext fun _ _ => Quotient.eq''

/--
theorem `ker_comp` / 定理 `ker_comp`

English:
theorem ker_comp
  given: {f : M ->+* N} {g : N ->+* P}
  proof: ext fun x y => by simp [ker_apply, comap_rel]

中文:
定理 ker_comp
  条件: {f : M ->+* N} {g : N ->+* P}
  证明: ext fun x y => by simp [ker_apply, comap_rel]

Depends on / 依赖: comap_rel, ker_apply
-/
theorem ker_comp {f : M ->+* N} {g : N ->+* P} :
    ker (g.comp f) = (ker g).comap f :=
  ext fun x y => by simp [ker_apply, comap_rel]

/--
theorem `comap_eq` / 定理 `comap_eq`

English:
theorem comap_eq
  given: {g : N ->+* M}
  proof: by
  rw [ker_comp]; rw [ker_mk'_eq]

中文:
定理 comap_eq
  条件: {g : N ->+* M}
  证明: by
  rw [ker_comp]; rw [ker_mk'_eq]

Depends on / 依赖: ker_comp, ker_mk
-/
theorem comap_eq {g : N ->+* M} :
    c.comap g = ker (c.mk'.comp g) := by
  rw [ker_comp]; rw [ker_mk'_eq]

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: {c : RingCon M} {d : RingCon N} (e : M ≃+* N) (h : c = d.comap e)
  body: Quotient.congr e by apply RingCon.ext_iff.mp h
  map_mul' := by rintro ⟨x⟩ ⟨y⟩; exact congrArg toQuotient (e.map_mul x y)
  map_add' := by rintro ⟨x⟩ ⟨y⟩; exact congrArg toQuotient (e.map_add x y)

中文:
定义 congr
  签名: {c : RingCon M} {d : RingCon N} (e : M ≃+* N) (h : c = d.comap e)
  定义体: Quotient.congr e by apply RingCon.ext_iff.mp h
  map_mul' := by rintro ⟨x⟩ ⟨y⟩; exact congrArg toQuotient (e.map_mul x y)
  map_add' := by rintro ⟨x⟩ ⟨y⟩; exact congrArg toQuotient (e.map_add x y)
-/
protected def congr {c : RingCon M} {d : RingCon N} (e : M ≃+* N) (h : c = d.comap e) :
    c.Quotient ≃+* d.Quotient where
__ := Quotient.congr e by apply RingCon.ext_iff.mp h
  map_mul' := by rintro ⟨x⟩ ⟨y⟩; exact congrArg toQuotient (e.map_mul x y)
  map_add' := by rintro ⟨x⟩ ⟨y⟩; exact congrArg toQuotient (e.map_add x y)

/--
theorem `congr_mk` / 定理 `congr_mk`

English:
theorem congr_mk
  given: {c : RingCon M} {d : RingCon N} (e : M ≃+* N) (h : c = d.comap e) (a : M)
  proof: rfl

中文:
定理 congr_mk
  条件: {c : RingCon M} {d : RingCon N} (e : M ≃+* N) (h : c = d.comap e) (a : M)
  证明: rfl
-/
@[simp] theorem congr_mk {c : RingCon M} {d : RingCon N} (e : M ≃+* N) (h : c = d.comap e) (a : M) :
    RingCon.congr e h (a : c.Quotient) = (e a : d.Quotient) := rfl

/--
theorem `congr_symm` / 定理 `congr_symm`

English:
theorem congr_symm
  given: {c : RingCon M} {d : RingCon N} (e : M ≃+* N) (h : c = d.comap e)
  proof: rfl

中文:
定理 congr_symm
  条件: {c : RingCon M} {d : RingCon N} (e : M ≃+* N) (h : c = d.comap e)
  证明: rfl
-/
@[simp] theorem congr_symm {c : RingCon M} {d : RingCon N} (e : M ≃+* N) (h : c = d.comap e) :
    (RingCon.congr e h).symm =
      RingCon.congr e.symm (ext <| e.surjective.forall₂.2 <| by simp [h]) :=
  rfl

/--
Definition of `mapGen` / `mapGen` 的定义

English:
definition mapGen
  signature: {c : RingCon M} (f : M -> N)
  body: ringConGen Relation.Map c f f

中文:
定义 mapGen
  签名: {c : RingCon M} (f : M -> N)
  定义体: ringConGen Relation.Map c f f

Depends on / 依赖: Relation, Relation.Map, ringConGen
-/
def mapGen {c : RingCon M} (f : M -> N) : RingCon N :=
ringConGen Relation.Map c f f

/--
theorem `mapGen_eq_map_of_surjective` / 定理 `mapGen_eq_map_of_surjective`

English:
theorem mapGen_eq_map_of_surjective
  proof: by
refine le_antisymm ?_ (RingCon.gi N).gc.le_u_l _
  have := Relation.map_equivalence c.toSetoid.2 _ hf h
  intro _ _ hg
  induction hg with
  | of _ _ a => exact a
  | refl x => exact this.refl x
  | symm _ h => exact this.symm h
  | trans _ _ h₁ h₂ => exact this.trans h₁ h₂
  | add _ _ h₁ h₂ =>
 

中文:
定理 mapGen_eq_map_of_surjective
  证明: by
refine le_antisymm ?_ (RingCon.gi N).gc.le_u_l _
  have := Relation.map_equivalence c.toSetoid.2 _ hf h
  intro _ _ hg
  induction hg with
  | of _ _ a => exact a
  | refl x => exact this.refl x
  | symm _ h => exact this.symm h
  | trans _ _ h₁ h₂ => exact this.trans h₁ h₂
  | add _ _ h₁ h₂ =>
 

Depends on / 依赖: Relation, Relation.map_equivalence, RingCon, RingCon.gi, c.add, c.toSetoid, gc.le_u_l, le_antisymm, le_u_l, map_add, map_equivalence, this.refl, this.symm, this.trans, toSetoid
-/
theorem mapGen_eq_map_of_surjective
    {c : RingCon M} (f : M ->+* N) (h : ker f <= c) (hf : Surjective f) :
    c.mapGen f = Relation.Map c f f := by
refine le_antisymm ?_ (RingCon.gi N).gc.le_u_l _
  have := Relation.map_equivalence c.toSetoid.2 _ hf h
  intro _ _ hg
  induction hg with
  | of _ _ a => exact a
  | refl x => exact this.refl x
  | symm _ h => exact this.symm h
  | trans _ _ h₁ h₂ => exact this.trans h₁ h₂
  | add _ _ h₁ h₂ =>
    rcases h₁ with ⟨a, b, h1, rfl, rfl⟩
    rcases h₂ with ⟨p, q, h2, rfl, rfl⟩
    exact ⟨a + p, b + q, c.add h1 h2, map_add f _ _, map_add f _ _⟩
  | mul _ _ h₁ h₂ =>
    rcases h₁ with ⟨a, b, h1, rfl, rfl⟩
    rcases h₂ with ⟨p, q, h2, rfl, rfl⟩
    exact ⟨a * p, b * q, c.mul h1 h2, map_mul f _ _, map_mul f _ _⟩

/--
theorem `mapGen_apply_apply_of_surjective` / 定理 `mapGen_apply_apply_of_surjective`

English:
theorem mapGen_apply_apply_of_surjective
  proof: by
  rw [mapGen_eq_map_of_surjective f h hf]; rw [Relation.map_apply]
  refine ⟨fun ⟨a, b, h₁, h₂, h₃⟩ => ?_, by grind⟩
exact c.trans (h h₂.symm) c.trans h₁ h h₃

中文:
定理 mapGen_apply_apply_of_surjective
  证明: by
  rw [mapGen_eq_map_of_surjective f h hf]; rw [Relation.map_apply]
  refine ⟨fun ⟨a, b, h₁, h₂, h₃⟩ => ?_, by grind⟩
exact c.trans (h h₂.symm) c.trans h₁ h h₃

Depends on / 依赖: Relation, Relation.map_apply, c.trans, mapGen_eq_map_of_surjective, map_apply
-/
theorem mapGen_apply_apply_of_surjective
    {c : RingCon M} (f : M ->+* N) (h : ker f <= c) (hf : Surjective f) {x y : M} :
    c.mapGen f (f x) (f y) ↔ c x y := by
  rw [mapGen_eq_map_of_surjective f h hf]; rw [Relation.map_apply]
  refine ⟨fun ⟨a, b, h₁, h₂, h₃⟩ => ?_, by grind⟩
exact c.trans (h h₂.symm) c.trans h₁ h h₃

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `correspondence` / `correspondence` 的定义

English:
definition correspondence
  signature: {c : RingCon M}
  body: d.1.mapGen c.mk'
invFun d := ⟨d.comap (mk' c), c.ker_mk'_eq.symm.trans_le comap_bot c.mk' ▸ comap_mono bot_le⟩
  left_inv d := by
    ext
    simp only [comap_rel]
    rw [mapGen_apply_apply_of_surjective c.mk' (c.ker_mk'_eq.trans_le d.2) c.mk'_surjective]
  right_inv d := by
    ext x y
    simp on

中文:
定义 correspondence
  签名: {c : RingCon M}
  定义体: d.1.mapGen c.mk'
invFun d := ⟨d.comap (mk' c), c.ker_mk'_eq.symm.trans_le comap_bot c.mk' ▸ comap_mono bot_le⟩
  left_inv d := by
    ext
    simp only [comap_rel]
    rw [mapGen_apply_apply_of_surjective c.mk' (c.ker_mk'_eq.trans_le d.2) c.mk'_surjective]
  right_inv d := by
    ext x y
    simp on

Depends on / 依赖: c.mk, mapGen
-/
def correspondence {c : RingCon M} : Set.Ici c ≃o RingCon c.Quotient where
  toFun d := d.1.mapGen c.mk'
invFun d := ⟨d.comap (mk' c), c.ker_mk'_eq.symm.trans_le comap_bot c.mk' ▸ comap_mono bot_le⟩
  left_inv d := by
    ext
    simp only [comap_rel]
    rw [mapGen_apply_apply_of_surjective c.mk' (c.ker_mk'_eq.trans_le d.2) c.mk'_surjective]
  right_inv d := by
    ext x y
    simp only
    obtain ⟨x, rfl⟩ := c.mk'_surjective x
    obtain ⟨y, rfl⟩ := c.mk'_surjective y
    rw [mapGen_apply_apply_of_surjective _ (comap_bot c.mk' ▸ comap_mono bot_le) c.mk'_surjective]; rw [comap_rel]
  map_rel_iff' {s t} := by
    simp only [Equiv.coe_fn_mk, le_def, c.mk'_surjective.forall, ← Subtype.coe_le_coe]
    simp_rw [mapGen_apply_apply_of_surjective c.mk' (c.ker_mk'_eq.trans_le s.2) c.mk'_surjective,
      mapGen_apply_apply_of_surjective c.mk' (c.ker_mk'_eq.trans_le t.2) c.mk'_surjective]

variable (c : RingCon M)

variable (x y : M)

variable (f : M ->+* P)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (H : c <= ker f)
  body: c.toAddCon.lift f.toAddMonoidHom H
  map_one' := f.map_one
  map_mul' x y := Con.induction_on₂ x y fun m n => f.map_mul m n

中文:
定义 lift
  签名: (H : c <= ker f)
  定义体: c.toAddCon.lift f.toAddMonoidHom H
  map_one' := f.map_one
  map_mul' x y := Con.induction_on₂ x y fun m n => f.map_mul m n

Depends on / 依赖: c.toAddCon.lift, f.toAddMonoidHom, toAddCon, toAddMonoidHom
-/
def lift (H : c <= ker f) : c.Quotient ->+* P where
  __ := c.toAddCon.lift f.toAddMonoidHom H
  map_one' := f.map_one
  map_mul' x y := Con.induction_on₂ x y fun m n => f.map_mul m n

variable {c f}

/--
theorem `lift_mk'` / 定理 `lift_mk'`

English:
theorem lift_mk'
  given: (H : c <= ker f) (x)
  statement: c.lift f H (c.mk' x) = f x
  proof: rfl

中文:
定理 lift_mk'
  条件: (H : c <= ker f) (x)
  结论: c.lift f H (c.mk' x) = f x
  证明: rfl
-/
theorem lift_mk' (H : c <= ker f) (x) : c.lift f H (c.mk' x) = f x :=
  rfl

/--
theorem `lift_coe` / 定理 `lift_coe`

English:
theorem lift_coe
  given: (H : c <= ker f) (x : M)
  statement: c.lift f H x = f x
  proof: rfl

中文:
定理 lift_coe
  条件: (H : c <= ker f) (x : M)
  结论: c.lift f H x = f x
  证明: rfl
-/
@[simp] theorem lift_coe (H : c <= ker f) (x : M) : c.lift f H x = f x :=
  rfl

/--
theorem `lift_comp_mk'` / 定理 `lift_comp_mk'`

English:
theorem lift_comp_mk'
  given: (H : c <= ker f)
  statement: (c.lift f H).comp c.mk' = f
  proof: rfl

中文:
定理 lift_comp_mk'
  条件: (H : c <= ker f)
  结论: (c.lift f H).comp c.mk' = f
  证明: rfl
-/
@[simp] theorem lift_comp_mk' (H : c <= ker f) : (c.lift f H).comp c.mk' = f := rfl

/--
theorem `lift_apply_mk'` / 定理 `lift_apply_mk'`

English:
theorem lift_apply_mk'
  given: (f : c.Quotient ->+* P)
  proof: by
  ext x; rcases x with ⟨⟩; rfl

中文:
定理 lift_apply_mk'
  条件: (f : c.商 ->+* P)
  证明: by
  ext x; rcases x with ⟨⟩; rfl
-/
theorem lift_apply_mk' (f : c.Quotient ->+* P) :
    (c.lift (f.comp c.mk') fun x y h => show f ↑x = f ↑y by rw [c.eq.2 h]) = f := by
  ext x; rcases x with ⟨⟩; rfl

/-- Homomorphisms on the quotient of a ring by a ring congruence relation are
equal if they are equal on elements that are coercions from the ring. -/
@[ext high] -- This should have higher priority than `RingHom.ext`
/--
theorem `Quotient.hom_ext` / 定理 `Quotient.hom_ext`

English:
theorem Quotient.hom_ext
  given: {f g : c.Quotient ->+* P} (h : f.comp c.mk' = g.comp c.mk')
  statement: f = g
  proof: DFunLike.ext _ _ c.mk'_surjective.forall.mpr fun x => by exact congr($h x)

中文:
定理 商.hom_ext
  条件: {f g : c.商 ->+* P} (h : f.comp c.mk' = g.comp c.mk')
  结论: f = g
  证明: DFunLike.ext _ _ c.mk'_surjective.forall.mpr fun x => by exact congr($h x)

Depends on / 依赖: DFunLike, DFunLike.ext, _surjective, _surjective.forall.mpr, c.mk
-/
theorem Quotient.hom_ext {f g : c.Quotient ->+* P} (h : f.comp c.mk' = g.comp c.mk') : f = g :=
DFunLike.ext _ _ c.mk'_surjective.forall.mpr fun x => by exact congr($h x)

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (H : c <= ker f) (g : c.Quotient ->+* P) (Hg : g.comp c.mk' = f)
  proof: Quotient.hom_ext (by aesop)

中文:
定理 lift_unique
  条件: (H : c <= ker f) (g : c.商 ->+* P) (Hg : g.comp c.mk' = f)
  证明: Quotient.hom_ext (by aesop)

Depends on / 依赖: Quotient, Quotient.hom_ext, hom_ext
-/
theorem lift_unique (H : c <= ker f) (g : c.Quotient ->+* P) (Hg : g.comp c.mk' = f) :
    g = c.lift f H :=
  Quotient.hom_ext (by aesop)

/--
theorem `lift_surjective_iff` / 定理 `lift_surjective_iff`

English:
theorem lift_surjective_iff
  given: {h : c <= ker f}
  proof: by
  refine ⟨fun H => (Quot.surjective_lift fun x x_1 h_1 => h h_1).mp H,
    fun H => AddCon.lift_surjective_of_surjective h H⟩

中文:
定理 lift_surjective_iff
  条件: {h : c <= ker f}
  证明: by
  refine ⟨fun H => (Quot.surjective_lift fun x x_1 h_1 => h h_1).mp H,
    fun H => AddCon.lift_surjective_of_surjective h H⟩

Depends on / 依赖: AddCon, AddCon.lift_surjective_of_surjective, Quot.surjective_lift, lift_surjective_of_surjective, surjective_lift
-/
theorem lift_surjective_iff {h : c <= ker f} :
    Surjective (c.lift f h) ↔ Surjective f := by
  refine ⟨fun H => (Quot.surjective_lift fun x x_1 h_1 => h h_1).mp H,
    fun H => AddCon.lift_surjective_of_surjective h H⟩

/--
theorem `lift_surjective_of_surjective` / 定理 `lift_surjective_of_surjective`

English:
theorem lift_surjective_of_surjective
  given: (h : c <= ker f) (hf : Surjective f)
  proof: lift_surjective_iff.mpr hf

中文:
定理 lift_surjective_of_surjective
  条件: (h : c <= ker f) (hf : 满射 f)
  证明: lift_surjective_iff.mpr hf

Depends on / 依赖: lift_surjective_iff, lift_surjective_iff.mpr
-/
theorem lift_surjective_of_surjective (h : c <= ker f) (hf : Surjective f) :
    Surjective (c.lift f h) :=
  lift_surjective_iff.mpr hf

/--
theorem `lift_injective_iff` / 定理 `lift_injective_iff`

English:
theorem lift_injective_iff
  given: {h : c <= ker f}
  proof: by
  refine ⟨fun H => ext'' (Setoid.ker_eq_lift_of_injective f h H).symm, ?_⟩
  rintro H ⟨x⟩ ⟨y⟩
  simp [H]

中文:
定理 lift_injective_iff
  条件: {h : c <= ker f}
  证明: by
  refine ⟨fun H => ext'' (Setoid.ker_eq_lift_of_injective f h H).symm, ?_⟩
  rintro H ⟨x⟩ ⟨y⟩
  simp [H]

Depends on / 依赖: Setoid, Setoid.ker_eq_lift_of_injective, ker_eq_lift_of_injective
-/
theorem lift_injective_iff {h : c <= ker f} :
    Function.Injective (c.lift f h) ↔ c = ker f := by
  refine ⟨fun H => ext'' (Setoid.ker_eq_lift_of_injective f h H).symm, ?_⟩
  rintro H ⟨x⟩ ⟨y⟩
  simp [H]

/--
theorem `lift_bijective_iff` / 定理 `lift_bijective_iff`

English:
theorem lift_bijective_iff
  given: {h : c <= ker f}
  proof: by
  unfold Function.Bijective
  simp only [lift_injective_iff, lift_surjective_iff]

中文:
定理 lift_bijective_iff
  条件: {h : c <= ker f}
  证明: by
  unfold Function.Bijective
  simp only [lift_injective_iff, lift_surjective_iff]

Depends on / 依赖: Bijective, Function, Function.Bijective, lift_injective_iff, lift_surjective_iff
-/
theorem lift_bijective_iff {h : c <= ker f} :
    Function.Bijective (c.lift f h) ↔ c = ker f ∧ Surjective f := by
  unfold Function.Bijective
  simp only [lift_injective_iff, lift_surjective_iff]

/--
theorem `ker_eq_lift_of_injective` / 定理 `ker_eq_lift_of_injective`

English:
theorem ker_eq_lift_of_injective
  given: (H : c <= ker f) (h : Injective (c.lift f H))
  statement: ker f = c
  proof: (lift_injective_iff.mp h).symm

中文:
定理 ker_eq_lift_of_injective
  条件: (H : c <= ker f) (h : 单射 (c.lift f H))
  结论: ker f = c
  证明: (lift_injective_iff.mp h).symm

Depends on / 依赖: lift_injective_iff, lift_injective_iff.mp
-/
theorem ker_eq_lift_of_injective (H : c <= ker f) (h : Injective (c.lift f H)) : ker f = c :=
  (lift_injective_iff.mp h).symm

variable (f)

/--
Definition of `kerLift` / `kerLift` 的定义

English:
definition kerLift
  signature: : (ker f).Quotient ->+* P
  body: (ker f).lift f fun _ _ => id

中文:
定义 kerLift
  签名: : (ker f).商 ->+* P
  定义体: (ker f).lift f fun _ _ => id
-/
def kerLift : (ker f).Quotient ->+* P :=
  (ker f).lift f fun _ _ => id

variable {f}

/--
theorem `kerLift_mk` / 定理 `kerLift_mk`

English:
theorem kerLift_mk
  given: (x : M)
  statement: kerLift f x = f x
  proof: rfl

中文:
定理 kerLift_mk
  条件: (x : M)
  结论: kerLift f x = f x
  证明: rfl
-/
theorem kerLift_mk (x : M) : kerLift f x = f x :=
  rfl

/--
theorem `kerLift_injective` / 定理 `kerLift_injective`

English:
theorem kerLift_injective
  given: (f : M ->+* P)
  statement: Injective (kerLift f)
  proof: AddCon.kerLift_injective (f : M ->+ P)

中文:
定理 kerLift_injective
  条件: (f : M ->+* P)
  结论: 单射 (kerLift f)
  证明: AddCon.kerLift_injective (f : M ->+ P)

Depends on / 依赖: AddCon, AddCon.kerLift_injective, kerLift_injective
-/
theorem kerLift_injective (f : M ->+* P) : Injective (kerLift f) :=
  AddCon.kerLift_injective (f : M ->+ P)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (c d : RingCon M) (h : c <= d)
  body: c.lift d.mk' fun x y hc => show ker d.mk' x y from (ker_mk'_eq d).symm ▸ h hc

中文:
定义 map
  签名: (c d : RingCon M) (h : c <= d)
  定义体: c.lift d.mk' fun x y hc => show ker d.mk' x y from (ker_mk'_eq d).symm ▸ h hc

Depends on / 依赖: c.lift, d.mk, ker_mk
-/
def map (c d : RingCon M) (h : c <= d) : c.Quotient ->+* d.Quotient :=
  c.lift d.mk' fun x y hc => show ker d.mk' x y from (ker_mk'_eq d).symm ▸ h hc

/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: {c d : RingCon M} (h : c <= d) (x)
  proof: rfl

中文:
定理 map_apply
  条件: {c d : RingCon M} (h : c <= d) (x)
  证明: rfl
-/
theorem map_apply {c d : RingCon M} (h : c <= d) (x) :
    c.map d h x = c.lift d.mk' (fun _ _ hc => d.eq.2 <| h hc) x :=
  rfl

end

section

variable [NonAssocSemiring M] [NonAssocSemiring N] [NonAssocSemiring P]

variable {c : RingCon M}

/--
theorem `rangeS_mk'` / 定理 `rangeS_mk'`

English:
theorem rangeS_mk'
  statement: RingHom.rangeS c.mk' = ⊤
  proof: RingHom.rangeS_eq_top.mpr (mk'_surjective _)

中文:
定理 rangeS_mk'
  结论: 环态射.rangeS c.mk' = ⊤
  证明: RingHom.rangeS_eq_top.mpr (mk'_surjective _)
-/
@[simp] theorem rangeS_mk' : RingHom.rangeS c.mk' = ⊤ :=
  RingHom.rangeS_eq_top.mpr (mk'_surjective _)

variable {f : M ->+* P}

/--
theorem `rangeS_lift` / 定理 `rangeS_lift`

English:
theorem rangeS_lift
  given: (H : c <= ker f)
  proof: SetLike.coe_injective Set.range_quot_lift _

中文:
定理 rangeS_lift
  条件: (H : c <= ker f)
  证明: SetLike.coe_injective Set.range_quot_lift _
-/
@[simp] theorem rangeS_lift (H : c <= ker f) :
    RingHom.rangeS (c.lift f H) = f.rangeS :=
SetLike.coe_injective Set.range_quot_lift _

/--
theorem `rangeS_kerLift` / 定理 `rangeS_kerLift`

English:
theorem rangeS_kerLift
  proof: rangeS_lift fun _ _ => id

中文:
定理 rangeS_kerLift
  证明: rangeS_lift fun _ _ => id
-/
@[simp] theorem rangeS_kerLift :
    RingHom.rangeS (kerLift f) = RingHom.rangeS f :=
  rangeS_lift fun _ _ => id

variable (c)

/--
Definition of `quotientKerEquivRangeS` / `quotientKerEquivRangeS` 的定义

English:
definition quotientKerEquivRangeS
  signature: (f : M ->+* P)
  body: RingHom.codRestrict (kerLift f) _ _
  __ := Setoid.quotientKerEquivRange _

中文:
定义 quotientKerEquivRangeS
  签名: (f : M ->+* P)
  定义体: RingHom.codRestrict (kerLift f) _ _
  __ := Setoid.quotientKerEquivRange _

Depends on / 依赖: RingHom, RingHom.codRestrict, codRestrict, kerLift
-/
noncomputable def quotientKerEquivRangeS (f : M ->+* P) :
    (ker f).Quotient ≃+* f.rangeS where
  __ := RingHom.codRestrict (kerLift f) _ _
  __ := Setoid.quotientKerEquivRange _

/--
theorem `coe_quotientKerEquivRangeS_mk` / 定理 `coe_quotientKerEquivRangeS_mk`

English:
theorem coe_quotientKerEquivRangeS_mk
  given: (f : M ->+* P) (x : M)
  proof: rfl

中文:
定理 coe_quotientKerEquivRangeS_mk
  条件: (f : M ->+* P) (x : M)
  证明: rfl
-/
@[simp] theorem coe_quotientKerEquivRangeS_mk (f : M ->+* P) (x : M) :
    (quotientKerEquivRangeS f x) = f x := rfl

/--
Definition of `quotientKerEquivOfRightInverse` / `quotientKerEquivOfRightInverse` 的定义

English:
definition quotientKerEquivOfRightInverse
  signature: (f : M ->+* P) (g : P -> M) (hf : Function.RightInverse g f)
  body: kerLift f
  __ := Setoid.quotientKerEquivOfRightInverse _ _ hf

中文:
定义 quotientKerEquivOfRightInverse
  签名: (f : M ->+* P) (g : P -> M) (hf : 函数.右逆 g f)
  定义体: kerLift f
  __ := Setoid.quotientKerEquivOfRightInverse _ _ hf

Depends on / 依赖: kerLift
-/
def quotientKerEquivOfRightInverse (f : M ->+* P) (g : P -> M) (hf : Function.RightInverse g f) :
    (ker f).Quotient ≃+* P where
  __ := kerLift f
  __ := Setoid.quotientKerEquivOfRightInverse _ _ hf

/--
theorem `quotientKerEquivOfRightInverse_apply` / 定理 `quotientKerEquivOfRightInverse_apply`

English:
theorem quotientKerEquivOfRightInverse_apply
  proof: rfl

中文:
定理 quotientKerEquivOfRightInverse_apply
  证明: rfl
-/
@[simp] theorem quotientKerEquivOfRightInverse_apply
    (f : M ->+* P) (g : P -> M) (hf : Function.RightInverse g f) (x : (ker f).Quotient) :
    quotientKerEquivOfRightInverse f g hf x = kerLift f x :=
  rfl

/--
Definition of `quotientKerEquivOfSurjective` / `quotientKerEquivOfSurjective` 的定义

English:
definition quotientKerEquivOfSurjective
  signature: (f : M ->+* P) (hf : Surjective f)
  body: quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec

中文:
定义 quotientKerEquivOfSurjective
  签名: (f : M ->+* P) (hf : 满射 f)
  定义体: quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec

Depends on / 依赖: choose_spec, hasRightInverse, hf.hasRightInverse.choose_spec, quotientKerEquivOfRightInverse
-/
noncomputable def quotientKerEquivOfSurjective (f : M ->+* P) (hf : Surjective f) :
    (ker f).Quotient ≃+* P :=
  quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec

/--
theorem `quotientKerEquivOfSurjective_mk` / 定理 `quotientKerEquivOfSurjective_mk`

English:
theorem quotientKerEquivOfSurjective_mk
  given: (f : M ->+* P) (hf : Surjective f) (x : M)
  proof: rfl

中文:
定理 quotientKerEquivOfSurjective_mk
  条件: (f : M ->+* P) (hf : 满射 f) (x : M)
  证明: rfl
-/
@[simp] theorem quotientKerEquivOfSurjective_mk (f : M ->+* P) (hf : Surjective f) (x : M) :
    quotientKerEquivOfSurjective f hf x = f x := rfl

/--
Definition of `comapQuotientEquivOfSurj` / `comapQuotientEquivOfSurj` 的定义

English:
definition comapQuotientEquivOfSurj
  body: (RingCon.congr (.refl _) (hcd.trans c.comap_eq)).trans
 RingCon.quotientKerEquivOfSurjective (c.mk'.comp f)
    (c.mk'_surjective.comp hf)

中文:
定义 comapQuotientEquivOfSurj
  定义体: (RingCon.congr (.refl _) (hcd.trans c.comap_eq)).trans
 RingCon.quotientKerEquivOfSurjective (c.mk'.comp f)
    (c.mk'_surjective.comp hf)

Depends on / 依赖: RingCon, RingCon.congr, RingCon.quotientKerEquivOfSurjective, _surjective, _surjective.comp, c.comap_eq, c.mk, comap_eq, hcd.trans, quotientKerEquivOfSurjective
-/
noncomputable def comapQuotientEquivOfSurj
    (c : RingCon M) (f : N ->+* M) (hf : Function.Surjective f)
    {d : RingCon N} (hcd : d = c.comap f) :
    d.Quotient ≃+* c.Quotient :=
  (RingCon.congr (.refl _) (hcd.trans c.comap_eq)).trans
 RingCon.quotientKerEquivOfSurjective (c.mk'.comp f)
    (c.mk'_surjective.comp hf)

/--
lemma `comapQuotientEquivOfSurj_mk` / 引理 `comapQuotientEquivOfSurj_mk`

English:
lemma comapQuotientEquivOfSurj_mk
  proof: rfl

中文:
引理 comapQuotientEquivOfSurj_mk
  证明: rfl
-/
@[simp] lemma comapQuotientEquivOfSurj_mk
    (c : RingCon M) {f : N ->+* M} (hf : Function.Surjective f)
    {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    c.comapQuotientEquivOfSurj f hf hcd x = f x := rfl

/--
lemma `comapQuotientEquivOfSurj_symm_mk` / 引理 `comapQuotientEquivOfSurj_symm_mk`

English:
lemma comapQuotientEquivOfSurj_symm_mk
  proof: by
  rw [← c.comapQuotientEquivOfSurj_mk hf hcd x]; rw [RingEquiv.symm_apply_apply]

中文:
引理 comapQuotientEquivOfSurj_symm_mk
  证明: by
  rw [← c.comapQuotientEquivOfSurj_mk hf hcd x]; rw [RingEquiv.symm_apply_apply]
-/
@[simp] lemma comapQuotientEquivOfSurj_symm_mk
    (c : RingCon M) {f : N ->+* M} (hf)
    {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    (c.comapQuotientEquivOfSurj f hf hcd).symm (f x) = x := by
  rw [← c.comapQuotientEquivOfSurj_mk hf hcd x]; rw [RingEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `comapQuotientEquivOfSurj_symm_mk'` / 引理 `comapQuotientEquivOfSurj_symm_mk'`

English:
lemma comapQuotientEquivOfSurj_symm_mk'
  statement: (c : RingCon M) (f : N ≃+* M)
  proof: by
  convert! RingEquiv.symm_apply_apply _ _
  rw [comapQuotientEquivOfSurj_mk]; rw [RingEquiv.coe_toRingHom]
  rfl

中文:
引理 comapQuotientEquivOfSurj_symm_mk'
  结论: (c : RingCon M) (f : N ≃+* M)
  证明: by
  convert! RingEquiv.symm_apply_apply _ _
  rw [comapQuotientEquivOfSurj_mk]; rw [RingEquiv.coe_toRingHom]
  rfl
-/
@[simp] lemma comapQuotientEquivOfSurj_symm_mk' (c : RingCon M) (f : N ≃+* M)
    {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    (comapQuotientEquivOfSurj c (f : N ->+* M) f.surjective hcd).symm ⟦f x⟧ = ↑x := by
  convert! RingEquiv.symm_apply_apply _ _
  rw [comapQuotientEquivOfSurj_mk]; rw [RingEquiv.coe_toRingHom]
  rfl

/--
Definition of `comapQuotientEquivRangeS` / `comapQuotientEquivRangeS` 的定义

English:
definition comapQuotientEquivRangeS
  signature: (f : N ->+* M)
  body: (RingCon.congr (.refl _) (hcd.trans comap_eq)).trans quotientKerEquivRangeS c.mk'.comp f

中文:
定义 comapQuotientEquivRangeS
  签名: (f : N ->+* M)
  定义体: (RingCon.congr (.refl _) (hcd.trans comap_eq)).trans quotientKerEquivRangeS c.mk'.comp f

Depends on / 依赖: RingCon, RingCon.congr, c.mk, comap_eq, hcd.trans, quotientKerEquivRangeS
-/
noncomputable def comapQuotientEquivRangeS (f : N ->+* M)
    {d : RingCon N} (hcd : d = comap c f) :
    d.Quotient ≃+* RingHom.rangeS (c.mk'.comp f) :=
(RingCon.congr (.refl _) (hcd.trans comap_eq)).trans quotientKerEquivRangeS c.mk'.comp f

/--
theorem `comapQuotientEquivRangeS_mk` / 定理 `comapQuotientEquivRangeS_mk`

English:
theorem comapQuotientEquivRangeS_mk
  statement: (f : N ->+* M)
  proof: rfl

中文:
定理 comapQuotientEquivRangeS_mk
  结论: (f : N ->+* M)
  证明: rfl
-/
@[simp] theorem comapQuotientEquivRangeS_mk (f : N ->+* M)
    {d : RingCon N} (hcd : d = comap c f) (x : N) :
    c.comapQuotientEquivRangeS f hcd x = ⟨f x, (c.mk'.comp f).mem_rangeS_self x⟩ :=
  rfl

/--
theorem `comapQuotientEquivRangeS_symm_mk` / 定理 `comapQuotientEquivRangeS_symm_mk`

English:
theorem comapQuotientEquivRangeS_symm_mk
  statement: (f : N ->+* M)
  proof: by
  simp [RingEquiv.symm_apply_eq]

中文:
定理 comapQuotientEquivRangeS_symm_mk
  结论: (f : N ->+* M)
  证明: by
  simp [RingEquiv.symm_apply_eq]
-/
@[simp] theorem comapQuotientEquivRangeS_symm_mk (f : N ->+* M)
    {d : RingCon N} (hcd : d = comap c f) (x : N) :
    (c.comapQuotientEquivRangeS f hcd).symm
      (⟨f x, RingHom.mem_rangeS_self (c.mk'.comp f) x ⟩) = x := by
  simp [RingEquiv.symm_apply_eq]

/--
Definition of `quotientQuotientEquivQuotient` / `quotientQuotientEquivQuotient` 的定义

English:
definition quotientQuotientEquivQuotient
  signature: (c d : RingCon M) (h : c <= d)
  body: { Setoid.quotientQuotientEquivQuotient c.toSetoid d.toSetoid h with
    map_add' x y :=
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a + d.mk' b by rw [← d.mk'.map_add]; rfl
    map_mul' x y :=
      Con.induction_on₂ x y fun w z =>
       

中文:
定义 quotientQuotientEquivQuotient
  签名: (c d : RingCon M) (h : c <= d)
  定义体: { Setoid.quotientQuotientEquivQuotient c.toSetoid d.toSetoid h with
    map_add' x y :=
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a + d.mk' b by rw [← d.mk'.map_add]; rfl
    map_mul' x y :=
      Con.induction_on₂ x y fun w z =>
       

Depends on / 依赖: Con.induction_on, Setoid, Setoid.quotientQuotientEquivQuotient, c.toSetoid, d.mk, d.toSetoid, map_add, map_mul, quotientQuotientEquivQuotient, toSetoid
-/
def quotientQuotientEquivQuotient (c d : RingCon M) (h : c <= d) :
    (RingCon.ker (c.map d h)).Quotient ≃+* d.Quotient :=
  { Setoid.quotientQuotientEquivQuotient c.toSetoid d.toSetoid h with
    map_add' x y :=
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a + d.mk' b by rw [← d.mk'.map_add]; rfl
    map_mul' x y :=
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a * d.mk' b by rw [← d.mk'.map_mul]; rfl }

/--
theorem `quotientQuotientEquivQuotient_mk_mk` / 定理 `quotientQuotientEquivQuotient_mk_mk`

English:
theorem quotientQuotientEquivQuotient_mk_mk
  given: (c d : RingCon M) (h : c <= d) (x : M)
  proof: rfl

中文:
定理 quotientQuotientEquivQuotient_mk_mk
  条件: (c d : RingCon M) (h : c <= d) (x : M)
  证明: rfl
-/
@[simp] theorem quotientQuotientEquivQuotient_mk_mk (c d : RingCon M) (h : c <= d) (x : M) :
    c.quotientQuotientEquivQuotient d h ⟦⟦x⟧⟧ = ⟦x⟧ := rfl

/--
theorem `quotientQuotientEquivQuotient_coe_coe` / 定理 `quotientQuotientEquivQuotient_coe_coe`

English:
theorem quotientQuotientEquivQuotient_coe_coe
  given: (c d : RingCon M) (h : c <= d) (x : M)
  proof: rfl

中文:
定理 quotientQuotientEquivQuotient_coe_coe
  条件: (c d : RingCon M) (h : c <= d) (x : M)
  证明: rfl
-/
@[simp] theorem quotientQuotientEquivQuotient_coe_coe (c d : RingCon M) (h : c <= d) (x : M) :
    c.quotientQuotientEquivQuotient d h ↑(x : c.Quotient) = x :=
  rfl

/--
theorem `quotientQuotientEquivQuotient_symm_mk` / 定理 `quotientQuotientEquivQuotient_symm_mk`

English:
theorem quotientQuotientEquivQuotient_symm_mk
  given: (c d : RingCon M) (h : c <= d) (x : M)
  proof: rfl

中文:
定理 quotientQuotientEquivQuotient_symm_mk
  条件: (c d : RingCon M) (h : c <= d) (x : M)
  证明: rfl
-/
@[simp] theorem quotientQuotientEquivQuotient_symm_mk (c d : RingCon M) (h : c <= d) (x : M) :
    (c.quotientQuotientEquivQuotient d h).symm ⟦x⟧ = ⟦⟦x⟧⟧ :=
  rfl

end

section

variable [Ring M] [Ring N] [Ring P]

variable {c : RingCon M}

/--
theorem `range_mk'` / 定理 `range_mk'`

English:
theorem range_mk'
  statement: RingHom.range c.mk' = ⊤
  proof: RingHom.range_eq_top.mpr (mk'_surjective _)

中文:
定理 range_mk'
  结论: 环态射.range c.mk' = ⊤
  证明: RingHom.range_eq_top.mpr (mk'_surjective _)

Depends on / 依赖: RingHom, RingHom.range_eq_top.mpr, _surjective, range_eq_top
-/
theorem range_mk' : RingHom.range c.mk' = ⊤ :=
  RingHom.range_eq_top.mpr (mk'_surjective _)

variable {f : M ->+* P}

/--
theorem `range_lift` / 定理 `range_lift`

English:
theorem range_lift
  given: (H : c <= ker f)
  proof: SetLike.coe_injective Set.range_quot_lift _

中文:
定理 range_lift
  条件: (H : c <= ker f)
  证明: SetLike.coe_injective Set.range_quot_lift _
-/
@[simp] theorem range_lift (H : c <= ker f) :
    RingHom.range (c.lift f H) = f.range :=
SetLike.coe_injective Set.range_quot_lift _

/--
theorem `kerLift_range_eq` / 定理 `kerLift_range_eq`

English:
theorem kerLift_range_eq
  proof: range_lift fun _ _ => id

中文:
定理 kerLift_range_eq
  证明: range_lift fun _ _ => id
-/
@[simp] theorem kerLift_range_eq :
    RingHom.range (kerLift f) = RingHom.range f :=
  range_lift fun _ _ => id

variable (c)

/--
Definition of `quotientKerEquivRange` / `quotientKerEquivRange` 的定义

English:
definition quotientKerEquivRange
  signature: (f : M ->+* P)
  body: quotientKerEquivRangeS f

中文:
定义 quotientKerEquivRange
  签名: (f : M ->+* P)
  定义体: quotientKerEquivRangeS f

Depends on / 依赖: quotientKerEquivRangeS
-/
noncomputable def quotientKerEquivRange (f : M ->+* P) :
    (ker f).Quotient ≃+* f.range :=
  quotientKerEquivRangeS f

/--
Definition of `comapQuotientEquivRange` / `comapQuotientEquivRange` 的定义

English:
definition comapQuotientEquivRange
  signature: (f : N ->+* M) {d : RingCon N} (hcd : d = c.comap f)
  body: c.comapQuotientEquivRangeS f hcd

中文:
定义 comapQuotientEquivRange
  签名: (f : N ->+* M) {d : RingCon N} (hcd : d = c.comap f)
  定义体: c.comapQuotientEquivRangeS f hcd

Depends on / 依赖: c.comapQuotientEquivRangeS, comapQuotientEquivRangeS
-/
noncomputable def comapQuotientEquivRange (f : N ->+* M) {d : RingCon N} (hcd : d = c.comap f) :
    d.Quotient ≃+* RingHom.range (c.mk'.comp f) :=
  c.comapQuotientEquivRangeS f hcd

/--
theorem `comapQuotientEquivRange_mk` / 定理 `comapQuotientEquivRange_mk`

English:
theorem comapQuotientEquivRange_mk
  proof: rfl

中文:
定理 comapQuotientEquivRange_mk
  证明: rfl
-/
theorem comapQuotientEquivRange_mk
    (f : N ->+* M) {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    c.comapQuotientEquivRange f hcd x = ⟨f x, (c.mk'.comp f).mem_range_self x⟩ :=
  rfl

/--
theorem `coe_comapQuotientEquivRange_mk` / 定理 `coe_comapQuotientEquivRange_mk`

English:
theorem coe_comapQuotientEquivRange_mk
  proof: rfl

中文:
定理 coe_comapQuotientEquivRange_mk
  证明: rfl
-/
@[simp] theorem coe_comapQuotientEquivRange_mk
    (f : N ->+* M) {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    (c.comapQuotientEquivRange f hcd x) = (f x : c.Quotient) :=
  rfl

/--
theorem `comapQuotientEquivRange_symm_mk` / 定理 `comapQuotientEquivRange_symm_mk`

English:
theorem comapQuotientEquivRange_symm_mk
  statement: (f : N ->+* M)
  proof: by
  simp [RingEquiv.symm_apply_eq, ← Subtype.coe_inj]

中文:
定理 comapQuotientEquivRange_symm_mk
  结论: (f : N ->+* M)
  证明: by
  simp [RingEquiv.symm_apply_eq, ← Subtype.coe_inj]
-/
@[simp] theorem comapQuotientEquivRange_symm_mk (f : N ->+* M)
    {d : RingCon N} (hcd : d = comap c f) (x : N) :
    (c.comapQuotientEquivRange f hcd).symm
      (⟨f x, RingHom.mem_range_self (c.mk'.comp f) x ⟩) = x := by
  simp [RingEquiv.symm_apply_eq, ← Subtype.coe_inj]

end

section

variable {R : Type*} [CommSemiring R]
  [Semiring M] [Algebra R M] [Semiring N] [Algebra R N] [Semiring P] [Algebra R P]

variable {c d : RingCon M} {f : M ->ₐ[R] P}

set_option backward.isDefEq.respectTransparency.types false in
variable (R) in
/--
Definition of `congrₐ` / `congrₐ` 的定义

English:
definition congrₐ
  signature: {c : RingCon M} {d : RingCon N} (e : M ≃ₐ[R] N) (h : c = d.comap e)
  body: RingCon.congr e h
  commutes' r := by simp [← coe_algebraMap]

@[simp]

中文:
定义 congrₐ
  签名: {c : RingCon M} {d : RingCon N} (e : M ≃ₐ[R] N) (h : c = d.comap e)
  定义体: RingCon.congr e h
  commutes' r := by simp [← coe_algebraMap]

@[simp]
-/
protected def congrₐ {c : RingCon M} {d : RingCon N} (e : M ≃ₐ[R] N) (h : c = d.comap e) :
    c.Quotient ≃ₐ[R] d.Quotient where
  __ := RingCon.congr e h
  commutes' r := by simp [← coe_algebraMap]

@[simp]
/--
theorem `congrₐ_mk` / 定理 `congrₐ_mk`

English:
theorem congrₐ_mk
  given: {c : RingCon M} {d : RingCon N} (e : M ≃ₐ[R] N) (h : c = d.comap e) (a : M)
  proof: rfl

中文:
定理 congrₐ_mk
  条件: {c : RingCon M} {d : RingCon N} (e : M ≃ₐ[R] N) (h : c = d.comap e) (a : M)
  证明: rfl
-/
theorem congrₐ_mk {c : RingCon M} {d : RingCon N} (e : M ≃ₐ[R] N) (h : c = d.comap e) (a : M) :
    RingCon.congrₐ R e h (a : c.Quotient) = (e a : d.Quotient) :=
  rfl

/--
theorem `congrₐ_symm` / 定理 `congrₐ_symm`

English:
theorem congrₐ_symm
  given: {c : RingCon M} {d : RingCon N} (e : M ≃ₐ[R] N) (h : c = d.comap e)
  proof: rfl

中文:
定理 congrₐ_symm
  条件: {c : RingCon M} {d : RingCon N} (e : M ≃ₐ[R] N) (h : c = d.comap e)
  证明: rfl
-/
@[simp] theorem congrₐ_symm {c : RingCon M} {d : RingCon N} (e : M ≃ₐ[R] N) (h : c = d.comap e) :
    (RingCon.congrₐ R e h).symm =
      RingCon.congrₐ R e.symm (ext <| e.surjective.forall₂.2 <| by simp [h]) :=
  rfl

/--
theorem `range_mkₐ` / 定理 `range_mkₐ`

English:
theorem range_mkₐ
  statement: AlgHom.range (mkₐ R c) = ⊤
  proof: (AlgHom.range_eq_top _).mpr (mkₐ_surjective _)

中文:
定理 range_mkₐ
  结论: 代数态射.range (mkₐ R c) = ⊤
  证明: (AlgHom.range_eq_top _).mpr (mkₐ_surjective _)

Depends on / 依赖: AlgHom, AlgHom.range_eq_top, range_eq_top
-/
theorem range_mkₐ : AlgHom.range (mkₐ R c) = ⊤ :=
  (AlgHom.range_eq_top _).mpr (mkₐ_surjective _)

/--
Definition of `liftₐ` / `liftₐ` 的定义

English:
definition liftₐ
  signature: (c : RingCon M) (f : M ->ₐ[R] P) (H : c <= ker f.toRingHom)
  body: { c.lift f H with
    commutes' r := AlgHomClass.commutes ↑f r }

中文:
定义 liftₐ
  签名: (c : RingCon M) (f : M ->ₐ[R] P) (H : c <= ker f.toRingHom)
  定义体: { c.lift f H with
    commutes' r := AlgHomClass.commutes ↑f r }

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, c.lift, commutes
-/
def liftₐ (c : RingCon M) (f : M ->ₐ[R] P) (H : c <= ker f.toRingHom) :
    c.Quotient ->ₐ[R] P :=
  { c.lift f H with
    commutes' r := AlgHomClass.commutes ↑f r }

/--
theorem `liftₐ_coe_toRingHom` / 定理 `liftₐ_coe_toRingHom`

English:
theorem liftₐ_coe_toRingHom
  given: (c : RingCon M) (f : M ->ₐ[R] P) (H : c <= ker f.toRingHom)
  proof: rfl

中文:
定理 liftₐ_coe_toRingHom
  条件: (c : RingCon M) (f : M ->ₐ[R] P) (H : c <= ker f.toRingHom)
  证明: rfl
-/
theorem liftₐ_coe_toRingHom (c : RingCon M) (f : M ->ₐ[R] P) (H : c <= ker f.toRingHom) :
    (c.liftₐ f H).toRingHom = c.lift f H :=
  rfl

/--
theorem `coe_liftₐ` / 定理 `coe_liftₐ`

English:
theorem coe_liftₐ
  given: (c : RingCon M) (f : M ->ₐ[R] P) (H : c <= ker f.toRingHom)
  proof: rfl

中文:
定理 coe_liftₐ
  条件: (c : RingCon M) (f : M ->ₐ[R] P) (H : c <= ker f.toRingHom)
  证明: rfl
-/
theorem coe_liftₐ (c : RingCon M) (f : M ->ₐ[R] P) (H : c <= ker f.toRingHom) :
    ⇑(c.liftₐ f H) = c.lift f H :=
  rfl

/--
theorem `liftₐ_mk` / 定理 `liftₐ_mk`

English:
theorem liftₐ_mk
  given: (c : RingCon M) (f : M ->ₐ[R] P) (H : c <= ker f.toRingHom) (x : M)
  proof: rfl

中文:
定理 liftₐ_mk
  条件: (c : RingCon M) (f : M ->ₐ[R] P) (H : c <= ker f.toRingHom) (x : M)
  证明: rfl
-/
@[simp] theorem liftₐ_mk (c : RingCon M) (f : M ->ₐ[R] P) (H : c <= ker f.toRingHom) (x : M) :
    c.liftₐ f H x = f x :=
  rfl

/--
theorem `liftₐ_range` / 定理 `liftₐ_range`

English:
theorem liftₐ_range
  given: (H : c <= ker f.toRingHom)
  proof: Subalgebra.toSubsemiring_injective rangeS_lift H

中文:
定理 liftₐ_range
  条件: (H : c <= ker f.toRingHom)
  证明: Subalgebra.toSubsemiring_injective rangeS_lift H

Depends on / 依赖: Subalgebra, Subalgebra.toSubsemiring_injective, rangeS_lift, toSubsemiring_injective
-/
theorem liftₐ_range (H : c <= ker f.toRingHom) :
    AlgHom.range (liftₐ c f H) = f.range :=
Subalgebra.toSubsemiring_injective rangeS_lift H

/-- Homomorphisms on the quotient of a ring by a ring congruence relation are
equal if they are equal on elements that are coercions from the ring. -/
-- This should have higher priority than `AlgHom.ext`, but lower than any types implemented with
-- `Quotient`, as `ext` is lax with reducibility.
@[ext 1100]
/--
theorem `Quotient.hom_extₐ` / 定理 `Quotient.hom_extₐ`

English:
theorem Quotient.hom_extₐ
  statement: {f g : c.Quotient ->ₐ[R] P}
  proof: DFunLike.ext _ _ c.mk'_surjective.forall.mpr fun x => by exact congr($h x)

中文:
定理 商.hom_extₐ
  结论: {f g : c.商 ->ₐ[R] P}
  证明: DFunLike.ext _ _ c.mk'_surjective.forall.mpr fun x => by exact congr($h x)

Depends on / 依赖: DFunLike, DFunLike.ext, _surjective, _surjective.forall.mpr, c.mk
-/
theorem Quotient.hom_extₐ {f g : c.Quotient ->ₐ[R] P}
    (h : f.comp (c.mkₐ R) = g.comp (c.mkₐ R)) : f = g :=
DFunLike.ext _ _ c.mk'_surjective.forall.mpr fun x => by exact congr($h x)

/-- `liftₐ` as an equivalence. -/
@[simps]
/--
Definition of `liftₐEquiv` / `liftₐEquiv` 的定义

English:
definition liftₐEquiv
  signature: (c : RingCon M)
  body: liftₐ c f.1 f.2
  invFun F := ⟨F.comp (c.mkₐ R), fun x y h => congr(F $(Quotient.sound h))⟩

中文:
定义 liftₐEquiv
  签名: (c : RingCon M)
  定义体: liftₐ c f.1 f.2
  invFun F := ⟨F.comp (c.mkₐ R), fun x y h => congr(F $(Quotient.sound h))⟩
-/
def liftₐEquiv (c : RingCon M) :
    { f : M ->ₐ[R] P // c <= ker (f : M ->+* P)} ≃ (c.Quotient ->ₐ[R] P) where
  toFun f := liftₐ c f.1 f.2
  invFun F := ⟨F.comp (c.mkₐ R), fun x y h => congr(F $(Quotient.sound h))⟩

variable (f) in
/--
Definition of `kerLiftₐ` / `kerLiftₐ` 的定义

English:
definition kerLiftₐ
  signature: : (ker f.toRingHom).Quotient ->ₐ[R] P
  body: liftₐ (ker f.toRingHom) f (le_refl _)

中文:
定义 kerLiftₐ
  签名: : (ker f.toRingHom).商 ->ₐ[R] P
  定义体: liftₐ (ker f.toRingHom) f (le_refl _)

Depends on / 依赖: f.toRingHom, le_refl, toRingHom
-/
def kerLiftₐ : (ker f.toRingHom).Quotient ->ₐ[R] P :=
  liftₐ (ker f.toRingHom) f (le_refl _)

/- Note : This can't be @[simp] because
  `(ker f.toRingHom).Quotient` is transformed into `(ker ↑f).Quotient`.
  Maybe `kerLiftₐ` should use the latter. -/
/--
theorem `kerLiftₐ_mk` / 定理 `kerLiftₐ_mk`

English:
theorem kerLiftₐ_mk
  given: (x : M)
  statement: kerLiftₐ f x = f x
  proof: by
  rfl

中文:
定理 kerLiftₐ_mk
  条件: (x : M)
  结论: kerLiftₐ f x = f x
  证明: by
  rfl
-/
theorem kerLiftₐ_mk (x : M) : kerLiftₐ f x = f x := by
  rfl

/--
theorem `kerLiftₐ_injective` / 定理 `kerLiftₐ_injective`

English:
theorem kerLiftₐ_injective
  given: (f : M ->ₐ[R] P)
  proof: kerLift_injective f.toRingHom

中文:
定理 kerLiftₐ_injective
  条件: (f : M ->ₐ[R] P)
  证明: kerLift_injective f.toRingHom

Depends on / 依赖: f.toRingHom, kerLift_injective, toRingHom
-/
theorem kerLiftₐ_injective (f : M ->ₐ[R] P) :
    Injective (kerLiftₐ f) := kerLift_injective f.toRingHom

variable (R) in
/--
Definition of `factorₐ` / `factorₐ` 的定义

English:
definition factorₐ
  signature: {c d : RingCon M} (h : c <= d)
  body: (liftₐ c (d.mkₐ R)) fun x y hc => show (ker d.mk') x y from (ker_mk'_eq d).symm ▸ h hc

中文:
定义 factorₐ
  签名: {c d : RingCon M} (h : c <= d)
  定义体: (liftₐ c (d.mkₐ R)) fun x y hc => show (ker d.mk') x y from (ker_mk'_eq d).symm ▸ h hc

Depends on / 依赖: d.mk, ker_mk
-/
def factorₐ {c d : RingCon M} (h : c <= d) :
    c.Quotient ->ₐ[R] d.Quotient :=
  (liftₐ c (d.mkₐ R)) fun x y hc => show (ker d.mk') x y from (ker_mk'_eq d).symm ▸ h hc

/--
theorem `factorₐ_apply` / 定理 `factorₐ_apply`

English:
theorem factorₐ_apply
  given: {c d : RingCon M} (h : c <= d) (x)
  proof: rfl

中文:
定理 factorₐ_apply
  条件: {c d : RingCon M} (h : c <= d) (x)
  证明: rfl
-/
theorem factorₐ_apply {c d : RingCon M} (h : c <= d) (x) :
    factorₐ R h x = liftₐ c (d.mkₐ R) (fun _ _ hc => d.eq.2 <| h hc) x :=
  rfl

/--
theorem `factorₐ_mk` / 定理 `factorₐ_mk`

English:
theorem factorₐ_mk
  given: {c d : RingCon M} (h : c <= d) (x : M)
  proof: rfl

中文:
定理 factorₐ_mk
  条件: {c d : RingCon M} (h : c <= d) (x : M)
  证明: rfl
-/
@[simp] theorem factorₐ_mk {c d : RingCon M} (h : c <= d) (x : M) :
    factorₐ R h ⟦x⟧ = ⟦x⟧ :=
  rfl

/--
theorem `mkₐ_comp_factorₐ_comp_mkₐ` / 定理 `mkₐ_comp_factorₐ_comp_mkₐ`

English:
theorem mkₐ_comp_factorₐ_comp_mkₐ
  given: {c d : RingCon M} (h : c <= d)
  proof: rfl

中文:
定理 mkₐ_comp_factorₐ_comp_mkₐ
  条件: {c d : RingCon M} (h : c <= d)
  证明: rfl
-/
@[simp] theorem mkₐ_comp_factorₐ_comp_mkₐ {c d : RingCon M} (h : c <= d) :
    (factorₐ R h).comp (c.mkₐ R) = d.mkₐ R :=
  rfl

/--
theorem `kerLiftₐ_range_eq` / 定理 `kerLiftₐ_range_eq`

English:
theorem kerLiftₐ_range_eq
  proof: liftₐ_range fun _ _ => id

中文:
定理 kerLiftₐ_range_eq
  证明: liftₐ_range fun _ _ => id
-/
@[simp] theorem kerLiftₐ_range_eq :
    AlgHom.range (kerLiftₐ f) = AlgHom.range f :=
  liftₐ_range fun _ _ => id

variable (c)

/--
Definition of `quotientKerEquivRangeₐ` / `quotientKerEquivRangeₐ` 的定义

English:
definition quotientKerEquivRangeₐ
  signature: (f : M ->ₐ[R] P)
  body: AlgHom.codRestrict (kerLiftₐ f) _ _
  __ := quotientKerEquivRangeS f.toRingHom

中文:
定义 quotientKerEquivRangeₐ
  签名: (f : M ->ₐ[R] P)
  定义体: AlgHom.codRestrict (kerLiftₐ f) _ _
  __ := quotientKerEquivRangeS f.toRingHom

Depends on / 依赖: AlgHom, AlgHom.codRestrict, codRestrict
-/
noncomputable def quotientKerEquivRangeₐ (f : M ->ₐ[R] P) :
    (ker (f : M ->+* P)).Quotient ≃ₐ[R] f.range where
  __ := AlgHom.codRestrict (kerLiftₐ f) _ _
  __ := quotientKerEquivRangeS f.toRingHom

/--
theorem `quotientKerEquivRangeₐ_mkₐ` / 定理 `quotientKerEquivRangeₐ_mkₐ`

English:
theorem quotientKerEquivRangeₐ_mkₐ
  given: (f : M ->ₐ[R] P) (x : M)
  proof: rfl

@[simp]

中文:
定理 quotientKerEquivRangeₐ_mkₐ
  条件: (f : M ->ₐ[R] P) (x : M)
  证明: rfl

@[simp]
-/
theorem quotientKerEquivRangeₐ_mkₐ (f : M ->ₐ[R] P) (x : M) :
    quotientKerEquivRangeₐ f x = ⟨f x, AlgHom.mem_range_self f x⟩ :=
  rfl

@[simp]
/--
theorem `coe_quotientKerEquivRangeₐ_mkₐ` / 定理 `coe_quotientKerEquivRangeₐ_mkₐ`

English:
theorem coe_quotientKerEquivRangeₐ_mkₐ
  given: (f : M ->ₐ[R] P) (x : M)
  proof: by
  rfl

中文:
定理 coe_quotientKerEquivRangeₐ_mkₐ
  条件: (f : M ->ₐ[R] P) (x : M)
  证明: by
  rfl
-/
theorem coe_quotientKerEquivRangeₐ_mkₐ (f : M ->ₐ[R] P) (x : M) :
    (quotientKerEquivRangeₐ f x : P) = f x := by
  rfl

/--
theorem `quotientKerEquivRangeₐ_comp_mkₐ` / 定理 `quotientKerEquivRangeₐ_comp_mkₐ`

English:
theorem quotientKerEquivRangeₐ_comp_mkₐ
  given: (φ : M ->ₐ[R] N)
  proof: rfl

中文:
定理 quotientKerEquivRangeₐ_comp_mkₐ
  条件: (φ : M ->ₐ[R] N)
  证明: rfl
-/
theorem quotientKerEquivRangeₐ_comp_mkₐ (φ : M ->ₐ[R] N) :
    ((quotientKerEquivRangeₐ φ).toAlgHom.comp ((ker (φ : M ->+* N)).mkₐ R)) = φ.rangeRestrict :=
  rfl

/--
Definition of `comapQuotientEquivRangeₐ` / `comapQuotientEquivRangeₐ` 的定义

English:
definition comapQuotientEquivRangeₐ
  signature: (f : N ->ₐ[R] M) {d : RingCon N} (h : d = comap c f)
  body: (RingCon.congrₐ R .refl (h.trans comap_eq)).trans quotientKerEquivRangeₐ ((c.mkₐ _).comp f)

中文:
定义 comapQuotientEquivRangeₐ
  签名: (f : N ->ₐ[R] M) {d : RingCon N} (h : d = comap c f)
  定义体: (RingCon.congrₐ R .refl (h.trans comap_eq)).trans quotientKerEquivRangeₐ ((c.mkₐ _).comp f)

Depends on / 依赖: RingCon, RingCon.congr, c.mk, comap_eq, h.trans
-/
noncomputable def comapQuotientEquivRangeₐ (f : N ->ₐ[R] M) {d : RingCon N} (h : d = comap c f) :
    d.Quotient ≃ₐ[R] AlgHom.range ((c.mkₐ _).comp f) :=
(RingCon.congrₐ R .refl (h.trans comap_eq)).trans quotientKerEquivRangeₐ ((c.mkₐ _).comp f)

/--
theorem `comapQuotientEquivRangeₐ_mk` / 定理 `comapQuotientEquivRangeₐ_mk`

English:
theorem comapQuotientEquivRangeₐ_mk
  given: (f : N ->ₐ[R] M) {d : RingCon N} (h : d = comap c f) (x : N)
  proof: rfl

中文:
定理 comapQuotientEquivRangeₐ_mk
  条件: (f : N ->ₐ[R] M) {d : RingCon N} (h : d = comap c f) (x : N)
  证明: rfl
-/
theorem comapQuotientEquivRangeₐ_mk (f : N ->ₐ[R] M) {d : RingCon N} (h : d = comap c f) (x : N) :
    c.comapQuotientEquivRangeₐ f h x = ⟨f x, AlgHom.mem_range_self _ x⟩ :=
  rfl

/--
theorem `coe_comapQuotientEquivRangeₐ_mk` / 定理 `coe_comapQuotientEquivRangeₐ_mk`

English:
theorem coe_comapQuotientEquivRangeₐ_mk
  proof: rfl

中文:
定理 coe_comapQuotientEquivRangeₐ_mk
  证明: rfl
-/
@[simp] theorem coe_comapQuotientEquivRangeₐ_mk
    (f : N ->ₐ[R] M) (x : N) {d : RingCon N} (h : d = comap c f) :
    (c.comapQuotientEquivRangeₐ f h x : c.Quotient) = f x :=
  rfl

/--
theorem `coe_comapQuotientEquivRangeₐ_symm_mk` / 定理 `coe_comapQuotientEquivRangeₐ_symm_mk`

English:
theorem coe_comapQuotientEquivRangeₐ_symm_mk
  proof: by
  simp [AlgEquiv.symm_apply_eq, ← Subtype.coe_inj]

中文:
定理 coe_comapQuotientEquivRangeₐ_symm_mk
  证明: by
  simp [AlgEquiv.symm_apply_eq, ← Subtype.coe_inj]
-/
@[simp] theorem coe_comapQuotientEquivRangeₐ_symm_mk
    (f : N ->ₐ[R] M) (x : N) {d : RingCon N} (h : d = c.comap f) :
    (c.comapQuotientEquivRangeₐ f h).symm (⟨f x, AlgHom.mem_range_self _ x⟩) = x := by
  simp [AlgEquiv.symm_apply_eq, ← Subtype.coe_inj]

variable (R)

/--
Definition of `quotientQuotientEquivQuotientₐ` / `quotientQuotientEquivQuotientₐ` 的定义

English:
definition quotientQuotientEquivQuotientₐ
  signature: {c d : RingCon M} (h : c <= d)
  body: { quotientQuotientEquivQuotient c d h with
    commutes' _ := by rfl }

@[simp]

中文:
定义 quotientQuotientEquivQuotientₐ
  签名: {c d : RingCon M} (h : c <= d)
  定义体: { quotientQuotientEquivQuotient c d h with
    commutes' _ := by rfl }

@[simp]

Depends on / 依赖: commutes, quotientQuotientEquivQuotient
-/
def quotientQuotientEquivQuotientₐ {c d : RingCon M} (h : c <= d) :
    (RingCon.ker (factorₐ R h : c.Quotient ->+* d.Quotient)).Quotient ≃ₐ[R] d.Quotient :=
  { quotientQuotientEquivQuotient c d h with
    commutes' _ := by rfl }

@[simp]
/--
theorem `quotientQuotientEquivQuotientₐ_mk_mk` / 定理 `quotientQuotientEquivQuotientₐ_mk_mk`

English:
theorem quotientQuotientEquivQuotientₐ_mk_mk
  given: {c d : RingCon M} (h : c <= d) (x : M)
  proof: rfl

@[simp]

中文:
定理 quotientQuotientEquivQuotientₐ_mk_mk
  条件: {c d : RingCon M} (h : c <= d) (x : M)
  证明: rfl

@[simp]
-/
theorem quotientQuotientEquivQuotientₐ_mk_mk {c d : RingCon M} (h : c <= d) (x : M) :
    quotientQuotientEquivQuotientₐ R h ⟦⟦x⟧⟧ = ⟦x⟧ := rfl

@[simp]
/--
theorem `quotientQuotientEquivQuotientₐ_coe_coe` / 定理 `quotientQuotientEquivQuotientₐ_coe_coe`

English:
theorem quotientQuotientEquivQuotientₐ_coe_coe
  given: {c d : RingCon M} (h : c <= d) (x : M)
  proof: quotientQuotientEquivQuotientₐ_mk_mk R h x

@[simp]

中文:
定理 quotientQuotientEquivQuotientₐ_coe_coe
  条件: {c d : RingCon M} (h : c <= d) (x : M)
  证明: quotientQuotientEquivQuotientₐ_mk_mk R h x

@[simp]
-/
theorem quotientQuotientEquivQuotientₐ_coe_coe {c d : RingCon M} (h : c <= d) (x : M) :
    quotientQuotientEquivQuotientₐ R h ↑(x : c.Quotient) = x :=
  quotientQuotientEquivQuotientₐ_mk_mk R h x

@[simp]
/--
theorem `quotientQuotientEquivQuotientₐ_symm_mk` / 定理 `quotientQuotientEquivQuotientₐ_symm_mk`

English:
theorem quotientQuotientEquivQuotientₐ_symm_mk
  given: {c d : RingCon M} (h : c <= d) (x : M)
  proof: rfl

中文:
定理 quotientQuotientEquivQuotientₐ_symm_mk
  条件: {c d : RingCon M} (h : c <= d) (x : M)
  证明: rfl
-/
theorem quotientQuotientEquivQuotientₐ_symm_mk {c d : RingCon M} (h : c <= d) (x : M) :
    (quotientQuotientEquivQuotientₐ R h).symm ⟦x⟧ = ⟦⟦x⟧⟧ :=
  rfl

end

end RingCon
