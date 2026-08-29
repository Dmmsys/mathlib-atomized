/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!

# Linear maps involving submodules of a module

In this file we define a number of linear maps involving submodules of a module.

## Main declarations

* `Submodule.subtype`: Embedding of a submodule `p` to the ambient space `M` as a `Submodule`.
* `LinearMap.domRestrict`: The restriction of a semilinear map `f : M → M₂` to a submodule `p ⊆ M`
  as a semilinear map `p → M₂`.
* `LinearMap.restrict`: The restriction of a linear map `f : M → M₁` to a submodule `p ⊆ M` and
  `q ⊆ M₁` (if `q` contains the codomain).
* `Submodule.inclusion`: the inclusion `p ⊆ p'` of submodules `p` and `p'` as a linear map.

## Tags

submodule, subspace, linear map
-/

@[expose] public section

open Function Set

universe u'' u' u v w

section

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

namespace SMulMemClass

variable [Semiring R] [AddCommMonoid M] [Module R M] {A : Type*} [SetLike A M]
  [AddSubmonoidClass A M] [SMulMemClass A R M] (S' : A)

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : S' ->ₗ[R] M where
  body: Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 subtype
  签名: : S' ->ₗ[R] M where
  定义体: Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
protected def subtype : S' ->ₗ[R] M where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {S'} in
@[simp]
/--
lemma `subtype_apply` / 引理 `subtype_apply`

English:
lemma subtype_apply
  given: (x : S')
  proof: rfl

中文:
引理 subtype_apply
  条件: (x : S')
  证明: rfl
-/
lemma subtype_apply (x : S') :
    SMulMemClass.subtype S' x = x := rfl

/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  proof: Subtype.coe_injective

@[simp]

中文:
引理 subtype_injective
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective :
    Function.Injective (SMulMemClass.subtype S') :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: (SMulMemClass.subtype S' : S' -> M) = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  结论: (SMulMemClass.subtype S' : S' -> M) = Subtype.val
  证明: rfl
-/
protected theorem coe_subtype : (SMulMemClass.subtype S' : S' -> M) = Subtype.val :=
  rfl

end SMulMemClass

namespace Submodule

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M]

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}
variable {p q : Submodule R M}
variable {r : R} {x y : M}
variable (p)

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : p ->ₗ[R] M where
  body: Subtype.val
  map_add' := by simp
  map_smul' := by simp

中文:
定义 subtype
  签名: : p ->ₗ[R] M where
  定义体: Subtype.val
  map_add' := by simp
  map_smul' := by simp
-/
protected def subtype : p ->ₗ[R] M where
  toFun := Subtype.val
  map_add' := by simp
  map_smul' := by simp

variable {p} in
@[simp]
/--
theorem `subtype_apply` / 定理 `subtype_apply`

English:
theorem subtype_apply
  given: (x : p)
  statement: p.subtype x = x
  proof: rfl

中文:
定理 subtype_apply
  条件: (x : p)
  结论: p.subtype x = x
  证明: rfl
-/
theorem subtype_apply (x : p) : p.subtype x = x :=
  rfl

/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  proof: Subtype.coe_injective

@[simp]

中文:
引理 subtype_injective
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective :
    Function.Injective p.subtype :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: (Submodule.subtype p : p -> M) = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  结论: (Submodule.subtype p : p -> M) = Subtype.val
  证明: rfl
-/
theorem coe_subtype : (Submodule.subtype p : p -> M) = Subtype.val :=
  rfl

/--
theorem `injective_subtype` / 定理 `injective_subtype`

English:
theorem injective_subtype
  statement: Injective p.subtype
  proof: Subtype.coe_injective

中文:
定理 injective_subtype
  结论: Injective p.subtype
  证明: Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem injective_subtype : Injective p.subtype :=
  Subtype.coe_injective

/--
theorem `coe_sum` / 定理 `coe_sum`

English:
theorem coe_sum
  given: (x : ι -> p) (s : Finset ι)
  statement: ↑(∑ i in s, x i) = ∑ i in s, (x i : M)
  proof: map_sum p.subtype _ _

中文:
定理 coe_sum
  条件: (x : ι -> p) (s : Finset ι)
  结论: ↑(∑ i in s, x i) = ∑ i in s, (x i : M)
  证明: map_sum p.subtype _ _

Depends on / 依赖: map_sum, p.subtype, subtype
-/
theorem coe_sum (x : ι -> p) (s : Finset ι) : ↑(∑ i in s, x i) = ∑ i in s, (x i : M) :=
  map_sum p.subtype _ _

section AddAction

variable {α β : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddAction
  signature: M α] : AddAction p α
  body: AddSubmonoid.instAddActionSubtypeMem p

中文:
实例 [AddAction
  签名: M α] : AddAction p α
  定义体: AddSubmonoid.instAddActionSubtypeMem p

Depends on / 依赖: AddSubmonoid, AddSubmonoid.instAddActionSubtypeMem, instAddActionSubtypeMem
-/
instance [AddAction M α] : AddAction p α :=
  AddSubmonoid.instAddActionSubtypeMem p

end AddAction

end AddCommMonoid

end Submodule

end

section

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {ι : Type*}

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₁] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R ->+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃)


/--
Definition of `domRestrict` / `domRestrict` 的定义

English:
definition domRestrict
  signature: (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M)
  body: f.comp p.subtype

@[simp]

中文:
定义 domRestrict
  签名: (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M)
  定义体: f.comp p.subtype

@[simp]

Depends on / 依赖: f.comp, p.subtype, subtype
-/
def domRestrict (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : p ->ₛₗ[σ₁₂] M₂ :=
  f.comp p.subtype

@[simp]
/--
theorem `domRestrict_apply` / 定理 `domRestrict_apply`

English:
theorem domRestrict_apply
  given: (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) (x : p)
  proof: rfl

中文:
定理 domRestrict_apply
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) (x : p)
  证明: rfl
-/
theorem domRestrict_apply (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) (x : p) :
    f.domRestrict p x = f x :=
  rfl

/--
lemma `coe_domRestrict` / 引理 `coe_domRestrict`

English:
lemma coe_domRestrict
  given: (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M)
  proof: rfl

中文:
引理 coe_domRestrict
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M)
  证明: rfl
-/
lemma coe_domRestrict (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    ⇑(f.domRestrict p) = Set.domRestrict p f := rfl

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (p : Submodule R₂ M₂) (f : M ->ₛₗ[σ₁₂] M₂) (h : forall c, f c in p)
  body: ⟨f c, h c⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp]

中文:
定义 codRestrict
  签名: (p : Submodule R₂ M₂) (f : M ->ₛₗ[σ₁₂] M₂) (h : 对任意 c, f c in p)
  定义体: ⟨f c, h c⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp]
-/
def codRestrict (p : Submodule R₂ M₂) (f : M ->ₛₗ[σ₁₂] M₂) (h : forall c, f c in p) : M ->ₛₗ[σ₁₂] p where
  toFun c := ⟨f c, h c⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp]
/--
theorem `codRestrict_apply` / 定理 `codRestrict_apply`

English:
theorem codRestrict_apply
  given: (p : Submodule R₂ M₂) (f : M ->ₛₗ[σ₁₂] M₂) {h} (x : M)
  proof: rfl

@[simp]

中文:
定理 codRestrict_apply
  条件: (p : Submodule R₂ M₂) (f : M ->ₛₗ[σ₁₂] M₂) {h} (x : M)
  证明: rfl

@[simp]
-/
theorem codRestrict_apply (p : Submodule R₂ M₂) (f : M ->ₛₗ[σ₁₂] M₂) {h} (x : M) :
    (codRestrict p f h x : M₂) = f x :=
  rfl

@[simp]
/--
theorem `comp_codRestrict` / 定理 `comp_codRestrict`

English:
theorem comp_codRestrict
  given: (p : Submodule R₃ M₃) (h : forall b, g b in p)
  proof: rfl

@[simp]

中文:
定理 comp_codRestrict
  条件: (p : Submodule R₃ M₃) (h : 对任意 b, g b in p)
  证明: rfl

@[simp]
-/
theorem comp_codRestrict (p : Submodule R₃ M₃) (h : forall b, g b in p) :
    ((codRestrict p g h).comp f : M ->ₛₗ[σ₁₃] p) = codRestrict p (g.comp f) fun _ => h _ :=
  rfl

@[simp]
/--
theorem `subtype_comp_codRestrict` / 定理 `subtype_comp_codRestrict`

English:
theorem subtype_comp_codRestrict
  given: (p : Submodule R₂ M₂) (h : forall b, f b in p)
  proof: rfl

@[simp]

中文:
定理 subtype_comp_codRestrict
  条件: (p : Submodule R₂ M₂) (h : 对任意 b, f b in p)
  证明: rfl

@[simp]
-/
theorem subtype_comp_codRestrict (p : Submodule R₂ M₂) (h : forall b, f b in p) :
    p.subtype.comp (codRestrict p f h) = f :=
  rfl

@[simp]
/--
theorem `domRestrict_comp_codRestrict` / 定理 `domRestrict_comp_codRestrict`

English:
theorem domRestrict_comp_codRestrict
  statement: (g : M₂ ->ₛₗ[σ₂₃] M₃) (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂)
  proof: rfl

中文:
定理 domRestrict_comp_codRestrict
  结论: (g : M₂ ->ₛₗ[σ₂₃] M₃) (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂)
  证明: rfl
-/
theorem domRestrict_comp_codRestrict (g : M₂ ->ₛₗ[σ₂₃] M₃) (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂)
    (h : forall c, f c in p) :
    g.domRestrict p ∘ₛₗ f.codRestrict p h = g ∘ₛₗ f :=
  rfl

section

variable {M₂' : Type*} [AddCommMonoid M₂'] [Module R₂ M₂']
  (p : M₂' ->ₗ[R₂] M₂) (hp : Injective p) (h : forall c, f c in range p)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `codLift` / `codLift` 的定义

English:
definition codLift
  signature: :
  body: (h c).choose
  map_add' b c := by apply hp; simp_rw [map_add, (h _).choose_spec, ← map_add, (h _).choose_spec]
  map_smul' r c := by apply hp; simp_rw [map_smul, (h _).choose_spec, map_smulₛₗ]

中文:
定义 codLift
  签名: :
  定义体: (h c).choose
  map_add' b c := by apply hp; simp_rw [map_add, (h _).choose_spec, ← map_add, (h _).choose_spec]
  map_smul' r c := by apply hp; simp_rw [map_smul, (h _).choose_spec, map_smulₛₗ]
-/
noncomputable def codLift :
    M ->ₛₗ[σ₁₂] M₂' where
  toFun c := (h c).choose
  map_add' b c := by apply hp; simp_rw [map_add, (h _).choose_spec, ← map_add, (h _).choose_spec]
  map_smul' r c := by apply hp; simp_rw [map_smul, (h _).choose_spec, map_smulₛₗ]

/--
theorem `codLift_apply` / 定理 `codLift_apply`

English:
theorem codLift_apply
  given: (x : M)
  proof: rfl

@[simp]

中文:
定理 codLift_apply
  条件: (x : M)
  证明: rfl

@[simp]
-/
@[simp] theorem codLift_apply (x : M) :
    (f.codLift p hp h x) = (h x).choose :=
  rfl

@[simp]
/--
theorem `comp_codLift` / 定理 `comp_codLift`

English:
theorem comp_codLift
  proof: by
  ext x
  rw [comp_apply]; rw [codLift_apply]; rw [(h x).choose_spec]

中文:
定理 comp_codLift
  证明: by
  ext x
  rw [comp_apply]; rw [codLift_apply]; rw [(h x).choose_spec]

Depends on / 依赖: choose_spec, codLift_apply, comp_apply
-/
theorem comp_codLift :
    p.comp (f.codLift p hp h) = f := by
  ext x
  rw [comp_apply]; rw [codLift_apply]; rw [(h x).choose_spec]

end

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (f : M ->ₛₗ[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂} (hf : forall x in p, f x in q)
  body: (f.domRestrict p).codRestrict q SetLike.forall.2 hf

@[simp]

中文:
定义 restrict
  签名: (f : M ->ₛₗ[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂} (hf : 对任意 x in p, f x in q)
  定义体: (f.domRestrict p).codRestrict q SetLike.forall.2 hf

@[simp]

Depends on / 依赖: SetLike, SetLike.forall, codRestrict, domRestrict, f.domRestrict
-/
def restrict (f : M ->ₛₗ[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂} (hf : forall x in p, f x in q) :
    p ->ₛₗ[σ₁₂] q :=
(f.domRestrict p).codRestrict q SetLike.forall.2 hf

@[simp]
/--
theorem `coe_restrict_apply` / 定理 `coe_restrict_apply`

English:
theorem coe_restrict_apply
  statement: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
  proof: rfl

@[deprecated coe_restrict_apply (since := "2026-05-13")]

中文:
定理 coe_restrict_apply
  结论: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
  证明: rfl

@[deprecated coe_restrict_apply (since := "2026-05-13")]
-/
theorem coe_restrict_apply {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
    (hf : forall x in p, f x in q) (x : p) : ↑(f.restrict hf x) = f x :=
  rfl

@[deprecated coe_restrict_apply (since := "2026-05-13")]
/--
theorem `restrict_coe_apply` / 定理 `restrict_coe_apply`

English:
theorem restrict_coe_apply
  statement: (f : M ->ₛₗ[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
  proof: rfl

中文:
定理 restrict_coe_apply
  结论: (f : M ->ₛₗ[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
  证明: rfl
-/
theorem restrict_coe_apply (f : M ->ₛₗ[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
    (hf : forall x in p, f x in q) (x : p) : ↑(f.restrict hf x) = f x :=
  rfl

/--
theorem `restrict_apply` / 定理 `restrict_apply`

English:
theorem restrict_apply
  statement: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
  proof: rfl

中文:
定理 restrict_apply
  结论: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
  证明: rfl
-/
theorem restrict_apply {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
    (hf : forall x in p, f x in q) (x : p) : f.restrict hf x = ⟨f x, hf x.1 x.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `restrict_sub` / 引理 `restrict_sub`

English:
lemma restrict_sub
  statement: {R R₂ M M₂ : Type*}
  proof: by
  ext; simp

中文:
引理 restrict_sub
  结论: {R R₂ M M₂ : 类型}
  证明: by
  ext; simp

Depends on / 依赖: q.sub_mem, sub_mem
-/
lemma restrict_sub {R R₂ M M₂ : Type*}
    [Ring R] [Ring R₂] {σ₁₂ : R ->+* R₂} [AddCommGroup M] [AddCommGroup M₂]
    [Module R M] [Module R₂ M₂] {p : Submodule R M} {q : Submodule R₂ M₂} {f g : M ->ₛₗ[σ₁₂] M₂}
    (hf : MapsTo f p q) (hg : MapsTo g p q)
    (hfg : MapsTo (f - g) p q := fun _ hx => q.sub_mem (hf hx) (hg hx)) :
    f.restrict hf - g.restrict hg = (f - g).restrict hfg := by
  ext; simp

/--
lemma `restrict_comp` / 引理 `restrict_comp`

English:
lemma restrict_comp
  statement: {p : Submodule R M} {p₂ : Submodule R₂ M₂} {p₃ : Submodule R₃ M₃}
  proof: rfl

中文:
引理 restrict_comp
  结论: {p : Submodule R M} {p₂ : Submodule R₂ M₂} {p₃ : Submodule R₃ M₃}
  证明: rfl

Depends on / 依赖: hg.comp
-/
lemma restrict_comp {p : Submodule R M} {p₂ : Submodule R₂ M₂} {p₃ : Submodule R₃ M₃}
    {f : M ->ₛₗ[σ₁₂] M₂} {g : M₂ ->ₛₗ[σ₂₃] M₃}
    (hf : MapsTo f p p₂) (hg : MapsTo g p₂ p₃) (hfg : MapsTo (g ∘ₛₗ f) p p₃ := hg.comp hf) :
    (g ∘ₛₗ f).restrict hfg = (g.restrict hg) ∘ₛₗ (f.restrict hf) :=
  rfl

-- TODO Consider defining `Algebra R (p.compatibleMaps p)`, `AlgHom` version of `LinearMap.restrict`
/--
lemma `restrict_smul_one` / 引理 `restrict_smul_one`

English:
lemma restrict_smul_one
  proof: rfl

中文:
引理 restrict_smul_one
  证明: rfl

Depends on / 依赖: p.smul_mem, smul_mem
-/
lemma restrict_smul_one
    {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {p : Submodule R M}
    (μ : R) (h : forall x in p, (μ • (1 : Module.End R M)) x in p := fun _ => p.smul_mem μ) :
    (μ • 1 : Module.End R M).restrict h = μ • (1 : Module.End R p) :=
  rfl

/--
lemma `restrict_commute` / 引理 `restrict_commute`

English:
lemma restrict_commute
  statement: {f g : M ->ₗ[R] M} (h : Commute f g) {p : Submodule R M}
  proof: by
  change (f ∘ₗ g).restrict (hf.comp hg) = (g ∘ₗ f).restrict (hg.comp hf)
  congr 1

中文:
引理 restrict_commute
  结论: {f g : M ->ₗ[R] M} (h : Commute f g) {p : Submodule R M}
  证明: by
  change (f ∘ₗ g).restrict (hf.comp hg) = (g ∘ₗ f).restrict (hg.comp hf)
  congr 1

Depends on / 依赖: hf.comp, hg.comp, restrict
-/
lemma restrict_commute {f g : M ->ₗ[R] M} (h : Commute f g) {p : Submodule R M}
    (hf : MapsTo f p p) (hg : MapsTo g p p) :
    Commute (f.restrict hf) (g.restrict hg) := by
  change (f ∘ₗ g).restrict (hf.comp hg) = (g ∘ₗ f).restrict (hg.comp hf)
  congr 1

/--
theorem `subtype_comp_restrict` / 定理 `subtype_comp_restrict`

English:
theorem subtype_comp_restrict
  statement: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
  proof: rfl

中文:
定理 subtype_comp_restrict
  结论: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
  证明: rfl
-/
theorem subtype_comp_restrict {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
    (hf : forall x in p, f x in q) : q.subtype.comp (f.restrict hf) = f.domRestrict p :=
  rfl

/--
theorem `restrict_eq_codRestrict_domRestrict` / 定理 `restrict_eq_codRestrict_domRestrict`

English:
theorem restrict_eq_codRestrict_domRestrict
  statement: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M}
  proof: rfl

中文:
定理 restrict_eq_codRestrict_domRestrict
  结论: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M}
  证明: rfl
-/
theorem restrict_eq_codRestrict_domRestrict {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M}
    {q : Submodule R₂ M₂} (hf : forall x in p, f x in q) :
    f.restrict hf = (f.domRestrict p).codRestrict q fun x => hf x.1 x.2 :=
  rfl

/--
theorem `restrict_eq_domRestrict_codRestrict` / 定理 `restrict_eq_domRestrict_codRestrict`

English:
theorem restrict_eq_domRestrict_codRestrict
  statement: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M}
  proof: rfl

中文:
定理 restrict_eq_domRestrict_codRestrict
  结论: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M}
  证明: rfl
-/
theorem restrict_eq_domRestrict_codRestrict {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M}
    {q : Submodule R₂ M₂} (hf : forall x, f x in q) :
    (f.restrict fun x _ => hf x) = (f.codRestrict q hf).domRestrict p :=
  rfl

/--
theorem `sum_apply` / 定理 `sum_apply`

English:
theorem sum_apply
  given: (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) (b : M)
  proof: _root_.map_sum ((AddMonoidHom.eval b).comp toAddMonoidHom') f _

@[simp, norm_cast]

中文:
定理 sum_apply
  条件: (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) (b : M)
  证明: _root_.map_sum ((AddMonoidHom.eval b).comp toAddMonoidHom') f _

@[simp, norm_cast]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.eval, _root_, _root_.map_sum, map_sum, toAddMonoidHom
-/
theorem sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) (b : M) :
    (∑ d in t, f d) b = ∑ d in t, f d b :=
  _root_.map_sum ((AddMonoidHom.eval b).comp toAddMonoidHom') f _

@[simp, norm_cast]
/--
theorem `coe_sum` / 定理 `coe_sum`

English:
theorem coe_sum
  given: {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂)
  proof: _root_.map_sum
    (show AddMonoidHom (M ->ₛₗ[σ₁₂] M₂) (M -> M₂)
      from { toFun := DFunLike.coe,
             map_zero' := rfl
             map_add' := fun _ _ => rfl }) _ _

中文:
定理 coe_sum
  条件: {ι : 类型} (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂)
  证明: _root_.map_sum
    (show AddMonoidHom (M ->ₛₗ[σ₁₂] M₂) (M -> M₂)
      from { toFun := DFunLike.coe,
             map_zero' := rfl
             map_add' := fun _ _ => rfl }) _ _

Depends on / 依赖: AddMonoidHom, DFunLike, DFunLike.coe, _root_, _root_.map_sum, map_add, map_sum, map_zero
-/
theorem coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) :
    ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂) :=
  _root_.map_sum
    (show AddMonoidHom (M ->ₛₗ[σ₁₂] M₂) (M -> M₂)
      from { toFun := DFunLike.coe,
             map_zero' := rfl
             map_add' := fun _ _ => rfl }) _ _

/--
theorem `_root_.Module.End.submodule_pow_eq_zero_of_pow_eq_zero` / 定理 `_root_.Module.End.submodule_pow_eq_zero_of_pow_eq_zero`

English:
theorem _root_.Module.End.submodule_pow_eq_zero_of_pow_eq_zero
  statement: {N : Submodule R M}
  proof: by
  ext m
  have hg : N.subtype.comp (g ^ k) m = 0 := by
    rw [← Module.End.commute_pow_left_of_commute h]; rw [hG]; rw [zero_comp]; rw [zero_apply]
  simpa using hg

中文:
定理 _root_.Module.End.submodule_pow_eq_zero_of_pow_eq_zero
  结论: {N : Submodule R M}
  证明: by
  ext m
  have hg : N.subtype.comp (g ^ k) m = 0 := by
    rw [← Module.End.commute_pow_left_of_commute h]; rw [hG]; rw [zero_comp]; rw [zero_apply]
  simpa using hg

Depends on / 依赖: Module, Module.End.commute_pow_left_of_commute, N.subtype.comp, commute_pow_left_of_commute, subtype, zero_apply, zero_comp
-/
theorem _root_.Module.End.submodule_pow_eq_zero_of_pow_eq_zero {N : Submodule R M}
    {g : Module.End R N} {G : Module.End R M} (h : G.comp N.subtype = N.subtype.comp g) {k : Nat}
    (hG : G ^ k = 0) : g ^ k = 0 := by
  ext m
  have hg : N.subtype.comp (g ^ k) m = 0 := by
    rw [← Module.End.commute_pow_left_of_commute h]; rw [hG]; rw [zero_comp]; rw [zero_apply]
  simpa using hg

section

variable {f' : M ->ₗ[R] M}

/--
theorem `_root_.Module.End.pow_apply_mem_of_forall_mem` / 定理 `_root_.Module.End.pow_apply_mem_of_forall_mem`

English:
theorem _root_.Module.End.pow_apply_mem_of_forall_mem
  statement: {p : Submodule R M} (n : Nat)
  proof: by
  induction n generalizing x with
  | zero => simpa
  | succ n ih =>
    simpa only [iterate_succ, coe_comp, Function.comp_apply, restrict_apply] using! ih _ (h _ hx)

中文:
定理 _root_.Module.End.pow_apply_mem_of_forall_mem
  结论: {p : Submodule R M} (n : 自然数)
  证明: by
  induction n generalizing x with
  | zero => simpa
  | succ n ih =>
    simpa only [iterate_succ, coe_comp, Function.comp_apply, restrict_apply] using! ih _ (h _ hx)

Depends on / 依赖: Function, Function.comp_apply, coe_comp, comp_apply, generalizing, iterate_succ, restrict_apply
-/
theorem _root_.Module.End.pow_apply_mem_of_forall_mem {p : Submodule R M} (n : Nat)
    (h : forall x in p, f' x in p) (x : M) (hx : x in p) : (f' ^ n) x in p := by
  induction n generalizing x with
  | zero => simpa
  | succ n ih =>
    simpa only [iterate_succ, coe_comp, Function.comp_apply, restrict_apply] using! ih _ (h _ hx)

/--
theorem `_root_.Module.End.pow_restrict` / 定理 `_root_.Module.End.pow_restrict`

English:
theorem _root_.Module.End.pow_restrict
  statement: {p : Submodule R M} (n : Nat) (h : forall x in p, f' x in p)
  proof: by
  ext x
  have : Semiconj (↑) (f'.restrict h) f' := fun _ => coe_restrict_apply _ _
  simp [Module.End.coe_pow, this.iterate_right _ _]

中文:
定理 _root_.Module.End.pow_restrict
  结论: {p : Submodule R M} (n : 自然数) (h : 对任意 x in p, f' x in p)
  证明: by
  ext x
  have : Semiconj (↑) (f'.restrict h) f' := fun _ => coe_restrict_apply _ _
  simp [Module.End.coe_pow, this.iterate_right _ _]

Depends on / 依赖: Module, Module.End.pow_apply_mem_of_forall_mem, pow_apply_mem_of_forall_mem
-/
theorem _root_.Module.End.pow_restrict {p : Submodule R M} (n : Nat) (h : forall x in p, f' x in p)
    (h' := Module.End.pow_apply_mem_of_forall_mem n h) :
    (f'.restrict h) ^ n = (f' ^ n).restrict h' := by
  ext x
  have : Semiconj (↑) (f'.restrict h) f' := fun _ => coe_restrict_apply _ _
  simp [Module.End.coe_pow, this.iterate_right _ _]

end

end AddCommMonoid

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]
variable (f g : M ->ₗ[R] M₂)

/--
Definition of `domRestrict'` / `domRestrict'` 的定义

English:
definition domRestrict'
  signature: (p : Submodule R M)
  body: φ.domRestrict p
  map_add' := by simp [LinearMap.ext_iff]
  map_smul' := by simp [LinearMap.ext_iff]

@[simp]

中文:
定义 domRestrict'
  签名: (p : Submodule R M)
  定义体: φ.domRestrict p
  map_add' := by simp [LinearMap.ext_iff]
  map_smul' := by simp [LinearMap.ext_iff]

@[simp]

Depends on / 依赖: domRestrict
-/
def domRestrict' (p : Submodule R M) : (M ->ₗ[R] M₂) ->ₗ[R] p ->ₗ[R] M₂ where
  toFun φ := φ.domRestrict p
  map_add' := by simp [LinearMap.ext_iff]
  map_smul' := by simp [LinearMap.ext_iff]

@[simp]
/--
theorem `domRestrict'_apply` / 定理 `domRestrict'_apply`

English:
theorem domRestrict'_apply
  given: (f : M ->ₗ[R] M₂) (p : Submodule R M) (x : p)
  proof: rfl

中文:
定理 domRestrict'_apply
  条件: (f : M ->ₗ[R] M₂) (p : Submodule R M) (x : p)
  证明: rfl
-/
theorem domRestrict'_apply (f : M ->ₗ[R] M₂) (p : Submodule R M) (x : p) :
    domRestrict' p f x = f x :=
  rfl

end CommSemiring

end LinearMap

end

namespace Submodule

section AddCommMonoid

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {p p' : Submodule R M}

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: (h : p <= p')
  body: p.subtype.codRestrict p' fun ⟨_, hx⟩ => h hx

@[simp]

中文:
定义 inclusion
  签名: (h : p <= p')
  定义体: p.subtype.codRestrict p' fun ⟨_, hx⟩ => h hx

@[simp]

Depends on / 依赖: codRestrict, p.subtype.codRestrict, subtype
-/
def inclusion (h : p <= p') : p ->ₗ[R] p' :=
  p.subtype.codRestrict p' fun ⟨_, hx⟩ => h hx

@[simp]
/--
theorem `coe_inclusion` / 定理 `coe_inclusion`

English:
theorem coe_inclusion
  given: (h : p <= p') (x : p)
  statement: (inclusion h x : M) = x
  proof: rfl

中文:
定理 coe_inclusion
  条件: (h : p <= p') (x : p)
  结论: (inclusion h x : M) = x
  证明: rfl
-/
theorem coe_inclusion (h : p <= p') (x : p) : (inclusion h x : M) = x :=
  rfl

/--
theorem `inclusion_apply` / 定理 `inclusion_apply`

English:
theorem inclusion_apply
  given: (h : p <= p') (x : p)
  statement: inclusion h x = ⟨x, h x.2⟩
  proof: rfl

中文:
定理 inclusion_apply
  条件: (h : p <= p') (x : p)
  结论: inclusion h x = ⟨x, h x.2⟩
  证明: rfl
-/
theorem inclusion_apply (h : p <= p') (x : p) : inclusion h x = ⟨x, h x.2⟩ :=
  rfl

/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  given: (h : p <= p')
  statement: Function.Injective (inclusion h)
  proof: fun _ _ h =>
  Subtype.val_injective (Subtype.mk.inj h)

中文:
定理 inclusion_injective
  条件: (h : p <= p')
  结论: Function.Injective (inclusion h)
  证明: fun _ _ h =>
  Subtype.val_injective (Subtype.mk.inj h)
-/
theorem inclusion_injective (h : p <= p') : Function.Injective (inclusion h) := fun _ _ h =>
  Subtype.val_injective (Subtype.mk.inj h)

variable (p p')

/--
theorem `subtype_comp_inclusion` / 定理 `subtype_comp_inclusion`

English:
theorem subtype_comp_inclusion
  given: (p q : Submodule R M) (h : p <= q)
  proof: rfl

中文:
定理 subtype_comp_inclusion
  条件: (p q : Submodule R M) (h : p <= q)
  证明: rfl
-/
theorem subtype_comp_inclusion (p q : Submodule R M) (h : p <= q) :
    q.subtype.comp (inclusion h) = p.subtype := rfl

end AddCommMonoid

end Submodule
