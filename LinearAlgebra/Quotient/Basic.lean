/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Quotients by submodules

* If `p` is a submodule of `M`, `M ⧸ p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.

## Main definitions

* `Submodule.Quotient.restrictScalarsEquiv`: The quotient of `P` as an `S`-submodule is the same
  as the quotient of `P` as an `R`-submodule,
* `Submodule.liftQ`: lift a map `M → M₂` to a map `M ⧸ p → M₂` if the kernel is contained in `p`
* `Submodule.mapQ`: lift a map `M → M₂` to a map `M ⧸ p → M₂ ⧸ q` if the image of `p` is contained
  in `q`

-/

@[expose] public section

assert_not_exists Cardinal

-- For most of this file we work over a noncommutative ring
section Ring

namespace Submodule

variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]
variable (p p' p'' : Submodule R M)

open LinearMap QuotientAddGroup

namespace Quotient

section Module

variable (S : Type*)

/--
Definition of `restrictScalarsEquiv` / `restrictScalarsEquiv` 的定义

English:
definition restrictScalarsEquiv
  signature: [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
  body: { Quotient.congrRight fun _ _ => Iff.rfl with
    map_add' := fun x y => Quotient.inductionOn₂' x y fun _x' _y' => rfl
    map_smul' := fun _c x => Submodule.Quotient.induction_on _ x fun _x' => rfl }

@[simp]

中文:
定义 restrictScalarsEquiv
  签名: [环 S] [标量乘法 S R] [模 S M] [标量塔 S R M]
  定义体: { Quotient.congrRight fun _ _ => Iff.rfl with
    map_add' := fun x y => Quotient.inductionOn₂' x y fun _x' _y' => rfl
    map_smul' := fun _c x => Submodule.Quotient.induction_on _ x fun _x' => rfl }

@[simp]

Depends on / 依赖: Iff.rfl, Quotient, Quotient.congrRight, Quotient.inductionOn, Submodule, Submodule.Quotient.induction_on, congrRight, induction_on, map_add, map_smul
-/
def restrictScalarsEquiv [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) : (M ⧸ P.restrictScalars S) ≃ₗ[S] M ⧸ P :=
  { Quotient.congrRight fun _ _ => Iff.rfl with
    map_add' := fun x y => Quotient.inductionOn₂' x y fun _x' _y' => rfl
    map_smul' := fun _c x => Submodule.Quotient.induction_on _ x fun _x' => rfl }

@[simp]
/--
theorem `restrictScalarsEquiv_mk` / 定理 `restrictScalarsEquiv_mk`

English:
theorem restrictScalarsEquiv_mk
  statement: [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
  proof: rfl

@[simp]

中文:
定理 restrictScalarsEquiv_mk
  结论: [环 S] [标量乘法 S R] [模 S M] [标量塔 S R M]
  证明: rfl

@[simp]
-/
theorem restrictScalarsEquiv_mk [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) (x : M) :
    restrictScalarsEquiv S P (mk x) = mk x :=
  rfl

@[simp]
/--
theorem `restrictScalarsEquiv_symm_mk` / 定理 `restrictScalarsEquiv_symm_mk`

English:
theorem restrictScalarsEquiv_symm_mk
  statement: [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
  proof: rfl

中文:
定理 restrictScalarsEquiv_symm_mk
  结论: [环 S] [标量乘法 S R] [模 S M] [标量塔 S R M]
  证明: rfl
-/
theorem restrictScalarsEquiv_symm_mk [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) (x : M) :
    (restrictScalarsEquiv S P).symm (mk x) = mk x :=
  rfl

end Module

variable {p}

/--
lemma `nontrivial_iff` / 引理 `nontrivial_iff`

English:
lemma nontrivial_iff
  statement: Nontrivial (M ⧸ p) ↔ p != ⊤
  proof: QuotientAddGroup.nontrivial_iff.trans (by simp)

中文:
引理 nontrivial_iff
  结论: 非平凡 (M ⧸ p) ↔ p != ⊤
  证明: QuotientAddGroup.nontrivial_iff.trans (by simp)
-/
@[simp] protected lemma nontrivial_iff : Nontrivial (M ⧸ p) ↔ p != ⊤ :=
  QuotientAddGroup.nontrivial_iff.trans (by simp)

/--
lemma `subsingleton_iff` / 引理 `subsingleton_iff`

English:
lemma subsingleton_iff
  statement: Subsingleton (M ⧸ p) ↔ p = ⊤
  proof: QuotientAddGroup.subsingleton_iff.trans (by simp)

中文:
引理 subsingleton_iff
  结论: 子单例 (M ⧸ p) ↔ p = ⊤
  证明: QuotientAddGroup.subsingleton_iff.trans (by simp)
-/
@[simp] protected lemma subsingleton_iff : Subsingleton (M ⧸ p) ↔ p = ⊤ :=
  QuotientAddGroup.subsingleton_iff.trans (by simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: M] : Subsingleton (M ⧸ p)
  body: by simpa using Subsingleton.elim ..

中文:
实例 [子单例
  签名: M] : 子单例 (M ⧸ p)
  定义体: by simpa using Subsingleton.elim ..

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance [Subsingleton M] : Subsingleton (M ⧸ p) := by simpa using Subsingleton.elim ..

end Quotient

/--
Instance `QuotientBot.infinite` / 实例 `QuotientBot.infinite`

English:
instance QuotientBot.infinite
  signature: [Infinite M]
  body: Infinite.of_injective Submodule.Quotient.mk fun _x _y h =>
sub_eq_zero.mp (Submodule.Quotient.eq ⊥).mp h

中文:
实例 QuotientBot.infinite
  签名: [无限 M]
  定义体: Infinite.of_injective Submodule.Quotient.mk fun _x _y h =>
sub_eq_zero.mp (Submodule.Quotient.eq ⊥).mp h

Depends on / 依赖: Infinite, Infinite.of_injective, Quotient, Submodule, Submodule.Quotient.eq, Submodule.Quotient.mk, of_injective, sub_eq_zero, sub_eq_zero.mp
-/
instance QuotientBot.infinite [Infinite M] : Infinite (M ⧸ (⊥ : Submodule R M)) :=
  Infinite.of_injective Submodule.Quotient.mk fun _x _y h =>
sub_eq_zero.mp (Submodule.Quotient.eq ⊥).mp h

/--
Instance `QuotientTop.unique` / 实例 `QuotientTop.unique`

English:
instance QuotientTop.unique
  signature: : Unique (M ⧸ (⊤ : Submodule R M)) where
  body: 0
  uniq x := Submodule.Quotient.induction_on _ x fun _x =>
    (Submodule.Quotient.eq ⊤).mpr Submodule.mem_top

中文:
实例 QuotientTop.unique
  签名: : 唯一 (M ⧸ (⊤ : 子模 R M)) where
  定义体: 0
  uniq x := Submodule.Quotient.induction_on _ x fun _x =>
    (Submodule.Quotient.eq ⊤).mpr Submodule.mem_top
-/
instance QuotientTop.unique : Unique (M ⧸ (⊤ : Submodule R M)) where
  default := 0
  uniq x := Submodule.Quotient.induction_on _ x fun _x =>
    (Submodule.Quotient.eq ⊤).mpr Submodule.mem_top

/--
Instance `QuotientTop.fintype` / 实例 `QuotientTop.fintype`

English:
instance QuotientTop.fintype
  signature: : Fintype (M ⧸ (⊤ : Submodule R M))
  body: Fintype.ofSubsingleton 0

中文:
实例 QuotientTop.fintype
  签名: : 有限类型 (M ⧸ (⊤ : 子模 R M))
  定义体: Fintype.ofSubsingleton 0

Depends on / 依赖: Fintype, Fintype.ofSubsingleton, ofSubsingleton
-/
instance QuotientTop.fintype : Fintype (M ⧸ (⊤ : Submodule R M)) :=
  Fintype.ofSubsingleton 0

variable {p} in
/--
theorem `unique_quotient_iff_eq_top` / 定理 `unique_quotient_iff_eq_top`

English:
theorem unique_quotient_iff_eq_top
  statement: Nonempty (Unique (M ⧸ p)) ↔ p = ⊤
  proof: ⟨fun ⟨h⟩ => Quotient.subsingleton_iff.mp (@Unique.instSubsingleton _ h),
    by rintro rfl; exact ⟨QuotientTop.unique⟩⟩

中文:
定理 unique_quotient_iff_eq_top
  结论: 非空 (唯一 (M ⧸ p)) ↔ p = ⊤
  证明: ⟨fun ⟨h⟩ => Quotient.subsingleton_iff.mp (@Unique.instSubsingleton _ h),
    by rintro rfl; exact ⟨QuotientTop.unique⟩⟩

Depends on / 依赖: Quotient, Quotient.subsingleton_iff.mp, QuotientTop, QuotientTop.unique, Unique, Unique.instSubsingleton, instSubsingleton, subsingleton_iff, unique
-/
theorem unique_quotient_iff_eq_top : Nonempty (Unique (M ⧸ p)) ↔ p = ⊤ :=
  ⟨fun ⟨h⟩ => Quotient.subsingleton_iff.mp (@Unique.instSubsingleton _ h),
    by rintro rfl; exact ⟨QuotientTop.unique⟩⟩

/--
Instance `Quotient.fintype` / 实例 `Quotient.fintype`

English:
instance Quotient.fintype
  signature: [Fintype M] (S : Submodule R M)
  body: @_root_.Quotient.fintype _ _ _ fun _ _ => Classical.dec _

中文:
实例 商.fintype
  签名: [有限类型 M] (S : 子模 R M)
  定义体: @_root_.Quotient.fintype _ _ _ fun _ _ => Classical.dec _
-/
noncomputable instance Quotient.fintype [Fintype M] (S : Submodule R M) : Fintype (M ⧸ S) :=
  @_root_.Quotient.fintype _ _ _ fun _ _ => Classical.dec _

section

variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]

/--
theorem `strictMono_comap_prod_map` / 定理 `strictMono_comap_prod_map`

English:
theorem strictMono_comap_prod_map
  proof: fun m₁ m₂ => QuotientAddGroup.strictMono_comap_prod_map
    p.toAddSubgroup (a := m₁.toAddSubgroup) (b := m₂.toAddSubgroup)

中文:
定理 strictMono_comap_prod_map
  证明: fun m₁ m₂ => QuotientAddGroup.strictMono_comap_prod_map
    p.toAddSubgroup (a := m₁.toAddSubgroup) (b := m₂.toAddSubgroup)

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.strictMono_comap_prod_map, p.toAddSubgroup, strictMono_comap_prod_map, toAddSubgroup
-/
theorem strictMono_comap_prod_map :
    StrictMono fun m : Submodule R M => (m.comap p.subtype, m.map p.mkQ) :=
  fun m₁ m₂ => QuotientAddGroup.strictMono_comap_prod_map
    p.toAddSubgroup (a := m₁.toAddSubgroup) (b := m₂.toAddSubgroup)

end

variable {R₂ M₂ : Type*} [Ring R₂] [AddCommGroup M₂] [Module R₂ M₂] {τ₁₂ : R ->+* R₂}

/--
Definition of `liftQ` / `liftQ` 的定义

English:
definition liftQ
  signature: (f : M ->ₛₗ[τ₁₂] M₂) (h : p <= ker f)
  body: { QuotientAddGroup.lift p.toAddSubgroup f.toAddMonoidHom h with
    map_smul' := by rintro a ⟨x⟩; exact f.map_smulₛₗ a x }

@[simp]

中文:
定义 liftQ
  签名: (f : M ->ₛₗ[τ₁₂] M₂) (h : p <= ker f)
  定义体: { QuotientAddGroup.lift p.toAddSubgroup f.toAddMonoidHom h with
    map_smul' := by rintro a ⟨x⟩; exact f.map_smulₛₗ a x }

@[simp]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.lift, f.map_smul, f.toAddMonoidHom, map_smul, p.toAddSubgroup, toAddMonoidHom, toAddSubgroup
-/
def liftQ (f : M ->ₛₗ[τ₁₂] M₂) (h : p <= ker f) : M ⧸ p ->ₛₗ[τ₁₂] M₂ :=
  { QuotientAddGroup.lift p.toAddSubgroup f.toAddMonoidHom h with
    map_smul' := by rintro a ⟨x⟩; exact f.map_smulₛₗ a x }

@[simp]
/--
theorem `liftQ_apply` / 定理 `liftQ_apply`

English:
theorem liftQ_apply
  given: (f : M ->ₛₗ[τ₁₂] M₂) {h} (x : M)
  statement: p.liftQ f h (Quotient.mk x) = f x
  proof: rfl

@[simp]

中文:
定理 liftQ_apply
  条件: (f : M ->ₛₗ[τ₁₂] M₂) {h} (x : M)
  结论: p.liftQ f h (商.mk x) = f x
  证明: rfl

@[simp]
-/
theorem liftQ_apply (f : M ->ₛₗ[τ₁₂] M₂) {h} (x : M) : p.liftQ f h (Quotient.mk x) = f x :=
  rfl

@[simp]
/--
theorem `liftQ_mkQ` / 定理 `liftQ_mkQ`

English:
theorem liftQ_mkQ
  given: (f : M ->ₛₗ[τ₁₂] M₂) (h)
  statement: (p.liftQ f h).comp p.mkQ = f
  proof: by ext; rfl

中文:
定理 liftQ_mkQ
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (h)
  结论: (p.liftQ f h).comp p.mkQ = f
  证明: by ext; rfl
-/
theorem liftQ_mkQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : (p.liftQ f h).comp p.mkQ = f := by ext; rfl

/--
theorem `pi_liftQ_eq_liftQ_pi` / 定理 `pi_liftQ_eq_liftQ_pi`

English:
theorem pi_liftQ_eq_liftQ_pi
  statement: {ι : Type*} {N : ι -> Type*}
  proof: by
  ext x i
  simp

中文:
定理 pi_liftQ_eq_liftQ_pi
  结论: {ι : 类型} {N : ι -> 类型}
  证明: by
  ext x i
  simp
-/
theorem pi_liftQ_eq_liftQ_pi {ι : Type*} {N : ι -> Type*}
    [forall i, AddCommGroup (N i)] [forall i, Module R (N i)]
    (f : (i : ι) -> M ->ₗ[R] (N i)) {p : Submodule R M} (h : forall i, p <= ker (f i)) :
    LinearMap.pi (fun i => p.liftQ (f i) (h i)) =
      p.liftQ (LinearMap.pi f) (LinearMap.ker_pi f ▸ le_iInf h) := by
  ext x i
  simp

/--
Definition of `liftQSpanSingleton` / `liftQSpanSingleton` 的定义

English:
definition liftQSpanSingleton
  signature: (x : M) (f : M ->ₛₗ[τ₁₂] M₂) (h : f x = 0)
  body: (R ∙ x).liftQ f by rw [span_singleton_le_iff_mem, LinearMap.mem_ker, h]

@[simp]

中文:
定义 liftQSpanSingleton
  签名: (x : M) (f : M ->ₛₗ[τ₁₂] M₂) (h : f x = 0)
  定义体: (R ∙ x).liftQ f by rw [span_singleton_le_iff_mem, LinearMap.mem_ker, h]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, mem_ker, span_singleton_le_iff_mem
-/
def liftQSpanSingleton (x : M) (f : M ->ₛₗ[τ₁₂] M₂) (h : f x = 0) : (M ⧸ R ∙ x) ->ₛₗ[τ₁₂] M₂ :=
(R ∙ x).liftQ f by rw [span_singleton_le_iff_mem, LinearMap.mem_ker, h]

@[simp]
/--
theorem `liftQSpanSingleton_apply` / 定理 `liftQSpanSingleton_apply`

English:
theorem liftQSpanSingleton_apply
  given: (x : M) (f : M ->ₛₗ[τ₁₂] M₂) (h : f x = 0) (y : M)
  proof: rfl

@[simp]

中文:
定理 liftQSpanSingleton_apply
  条件: (x : M) (f : M ->ₛₗ[τ₁₂] M₂) (h : f x = 0) (y : M)
  证明: rfl

@[simp]
-/
theorem liftQSpanSingleton_apply (x : M) (f : M ->ₛₗ[τ₁₂] M₂) (h : f x = 0) (y : M) :
    liftQSpanSingleton x f h (Quotient.mk y) = f y :=
  rfl

@[simp]
/--
theorem `range_mkQ` / 定理 `range_mkQ`

English:
theorem range_mkQ
  statement: range p.mkQ = ⊤
  proof: eq_top_iff'.2 by rintro ⟨x⟩; exact ⟨x, rfl⟩

@[simp]

中文:
定理 range_mkQ
  结论: range p.mkQ = ⊤
  证明: eq_top_iff'.2 by rintro ⟨x⟩; exact ⟨x, rfl⟩

@[simp]

Depends on / 依赖: eq_top_iff
-/
theorem range_mkQ : range p.mkQ = ⊤ :=
eq_top_iff'.2 by rintro ⟨x⟩; exact ⟨x, rfl⟩

@[simp]
/--
theorem `ker_mkQ` / 定理 `ker_mkQ`

English:
theorem ker_mkQ
  statement: ker p.mkQ = p
  proof: by ext; simp

中文:
定理 ker_mkQ
  结论: ker p.mkQ = p
  证明: by ext; simp
-/
theorem ker_mkQ : ker p.mkQ = p := by ext; simp

/--
theorem `le_comap_mkQ` / 定理 `le_comap_mkQ`

English:
theorem le_comap_mkQ
  given: (p' : Submodule R (M ⧸ p))
  statement: p <= comap p.mkQ p'
  proof: by
  simpa using (comap_mono bot_le : ker p.mkQ <= comap p.mkQ p')

@[simp]

中文:
定理 le_comap_mkQ
  条件: (p' : 子模 R (M ⧸ p))
  结论: p <= comap p.mkQ p'
  证明: by
  simpa using (comap_mono bot_le : ker p.mkQ <= comap p.mkQ p')

@[simp]

Depends on / 依赖: bot_le, comap_mono, p.mkQ
-/
theorem le_comap_mkQ (p' : Submodule R (M ⧸ p)) : p <= comap p.mkQ p' := by
  simpa using (comap_mono bot_le : ker p.mkQ <= comap p.mkQ p')

@[simp]
/--
theorem `mkQ_map_self` / 定理 `mkQ_map_self`

English:
theorem mkQ_map_self
  statement: map p.mkQ p = ⊥
  proof: by
  rw [eq_bot_iff]; rw [map_le_iff_le_comap]; rw [comap_bot]; rw [ker_mkQ]

@[simp]

中文:
定理 mkQ_map_self
  结论: map p.mkQ p = ⊥
  证明: by
  rw [eq_bot_iff]; rw [map_le_iff_le_comap]; rw [comap_bot]; rw [ker_mkQ]

@[simp]

Depends on / 依赖: comap_bot, eq_bot_iff, ker_mkQ, map_le_iff_le_comap
-/
theorem mkQ_map_self : map p.mkQ p = ⊥ := by
  rw [eq_bot_iff]; rw [map_le_iff_le_comap]; rw [comap_bot]; rw [ker_mkQ]

@[simp]
/--
theorem `comap_map_mkQ` / 定理 `comap_map_mkQ`

English:
theorem comap_map_mkQ
  statement: comap p.mkQ (map p.mkQ p') = p ⊔ p'
  proof: by simp [comap_map_eq, sup_comm]

@[simp]

中文:
定理 comap_map_mkQ
  结论: comap p.mkQ (map p.mkQ p') = p ⊔ p'
  证明: by simp [comap_map_eq, sup_comm]

@[simp]

Depends on / 依赖: comap_map_eq, sup_comm
-/
theorem comap_map_mkQ : comap p.mkQ (map p.mkQ p') = p ⊔ p' := by simp [comap_map_eq, sup_comm]

@[simp]
/--
theorem `map_mkQ_eq_top` / 定理 `map_mkQ_eq_top`

English:
theorem map_mkQ_eq_top
  statement: map p.mkQ p' = ⊤ ↔ p ⊔ p' = ⊤
  proof: by
  simp only [LinearMap.map_eq_top_iff p.range_mkQ, sup_comm, ker_mkQ]

中文:
定理 map_mkQ_eq_top
  结论: map p.mkQ p' = ⊤ ↔ p ⊔ p' = ⊤
  证明: by
  simp only [LinearMap.map_eq_top_iff p.range_mkQ, sup_comm, ker_mkQ]

Depends on / 依赖: LinearMap, LinearMap.map_eq_top_iff, ker_mkQ, map_eq_top_iff, p.range_mkQ, range_mkQ, sup_comm
-/
theorem map_mkQ_eq_top : map p.mkQ p' = ⊤ ↔ p ⊔ p' = ⊤ := by
  simp only [LinearMap.map_eq_top_iff p.range_mkQ, sup_comm, ker_mkQ]

variable (q : Submodule R₂ M₂)

/--
Definition of `mapQ` / `mapQ` 的定义

English:
definition mapQ
  signature: (f : M ->ₛₗ[τ₁₂] M₂) (h : p <= comap f q)
  body: p.liftQ (q.mkQ.comp f) by simpa [ker_comp] using h

@[simp]

中文:
定义 mapQ
  签名: (f : M ->ₛₗ[τ₁₂] M₂) (h : p <= comap f q)
  定义体: p.liftQ (q.mkQ.comp f) by simpa [ker_comp] using h

@[simp]

Depends on / 依赖: ker_comp, p.liftQ, q.mkQ.comp
-/
def mapQ (f : M ->ₛₗ[τ₁₂] M₂) (h : p <= comap f q) : M ⧸ p ->ₛₗ[τ₁₂] M₂ ⧸ q :=
p.liftQ (q.mkQ.comp f) by simpa [ker_comp] using h

@[simp]
/--
theorem `mapQ_apply` / 定理 `mapQ_apply`

English:
theorem mapQ_apply
  given: (f : M ->ₛₗ[τ₁₂] M₂) {h} (x : M)
  proof: rfl

中文:
定理 mapQ_apply
  条件: (f : M ->ₛₗ[τ₁₂] M₂) {h} (x : M)
  证明: rfl
-/
theorem mapQ_apply (f : M ->ₛₗ[τ₁₂] M₂) {h} (x : M) :
    mapQ p q f h (Quotient.mk x) = Quotient.mk (f x) :=
  rfl

/--
theorem `mapQ_mkQ` / 定理 `mapQ_mkQ`

English:
theorem mapQ_mkQ
  given: (f : M ->ₛₗ[τ₁₂] M₂) {h}
  statement: (mapQ p q f h).comp p.mkQ = q.mkQ.comp f
  proof: by
  ext x; rfl

@[simp]

中文:
定理 mapQ_mkQ
  条件: (f : M ->ₛₗ[τ₁₂] M₂) {h}
  结论: (mapQ p q f h).comp p.mkQ = q.mkQ.comp f
  证明: by
  ext x; rfl

@[simp]
-/
theorem mapQ_mkQ (f : M ->ₛₗ[τ₁₂] M₂) {h} : (mapQ p q f h).comp p.mkQ = q.mkQ.comp f := by
  ext x; rfl

@[simp]
/--
theorem `mapQ_zero` / 定理 `mapQ_zero`

English:
theorem mapQ_zero
  given: (h : p <= q.comap (0 : M ->ₛₗ[τ₁₂] M₂) := (by simp))
  proof: by
  ext
  simp

中文:
定理 mapQ_zero
  条件: (h : p <= q.comap (0 : M ->ₛₗ[τ₁₂] M₂) := (by simp))
  证明: by
  ext
  simp
-/
theorem mapQ_zero (h : p <= q.comap (0 : M ->ₛₗ[τ₁₂] M₂) := (by simp)) :
    p.mapQ q (0 : M ->ₛₗ[τ₁₂] M₂) h = 0 := by
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mapQ_comp` / 定理 `mapQ_comp`

English:
theorem mapQ_comp
  statement: {R₃ M₃ : Type*} [Ring R₃] [AddCommGroup M₃] [Module R₃ M₃] (p₂ : Submodule R₂ M₂)
  proof: by
  ext
  simp

@[simp]

中文:
定理 mapQ_comp
  结论: {R₃ M₃ : 类型} [环 R₃] [加法交换群 M₃] [模 R₃ M₃] (p₂ : 子模 R₂ M₂)
  证明: by
  ext
  simp

@[simp]

Depends on / 依赖: comap_mono, hf.trans
-/
theorem mapQ_comp {R₃ M₃ : Type*} [Ring R₃] [AddCommGroup M₃] [Module R₃ M₃] (p₂ : Submodule R₂ M₂)
    (p₃ : Submodule R₃ M₃) {τ₂₃ : R₂ ->+* R₃} {τ₁₃ : R ->+* R₃} [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]
    (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) (hf : p <= p₂.comap f) (hg : p₂ <= p₃.comap g)
    (h := hf.trans (comap_mono hg)) :
    p.mapQ p₃ (g.comp f) h = (p₂.mapQ p₃ g hg).comp (p.mapQ p₂ f hf) := by
  ext
  simp

@[simp]
/--
theorem `mapQ_id` / 定理 `mapQ_id`

English:
theorem mapQ_id
  given: (h : p <= p.comap LinearMap.id := (by rw [comap_id]))
  proof: by
  ext
  simp

中文:
定理 mapQ_id
  条件: (h : p <= p.comap 线性映射.id := (by rw [comap_id]))
  证明: by
  ext
  simp

Depends on / 依赖: comap_id
-/
theorem mapQ_id (h : p <= p.comap LinearMap.id := (by rw [comap_id])) :
    p.mapQ p LinearMap.id h = LinearMap.id := by
  ext
  simp

/--
theorem `mapQ_pow` / 定理 `mapQ_pow`

English:
theorem mapQ_pow
  statement: {f : M ->ₗ[R] M} (h : p <= p.comap f) (k : Nat)
  proof: by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih =>
    simp only [Module.End.iterate_succ]
    rw [mapQ_comp]; rw [ih]
    exact p.le_comap_pow_of_le_comap h k

中文:
定理 mapQ_pow
  结论: {f : M ->ₗ[R] M} (h : p <= p.comap f) (k : 自然数)
  证明: by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih =>
    simp only [Module.End.iterate_succ]
    rw [mapQ_comp]; rw [ih]
    exact p.le_comap_pow_of_le_comap h k

Depends on / 依赖: le_comap_pow_of_le_comap, p.le_comap_pow_of_le_comap
-/
theorem mapQ_pow {f : M ->ₗ[R] M} (h : p <= p.comap f) (k : Nat)
    (h' : p <= p.comap (f ^ k) := p.le_comap_pow_of_le_comap h k) :
    p.mapQ p (f ^ k) h' = p.mapQ p f h ^ k := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih =>
    simp only [Module.End.iterate_succ]
    rw [mapQ_comp]; rw [ih]
    exact p.le_comap_pow_of_le_comap h k

/--
theorem `comap_liftQ` / 定理 `comap_liftQ`

English:
theorem comap_liftQ
  given: (f : M ->ₛₗ[τ₁₂] M₂) (h)
  statement: q.comap (p.liftQ f h) = (q.comap f).map (mkQ p)
  proof: le_antisymm (by rintro ⟨x⟩ hx; exact ⟨_, hx, rfl⟩)
    (by rw [map_le_iff_le_comap, ← comap_comp, liftQ_mkQ])

中文:
定理 comap_liftQ
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (h)
  结论: q.comap (p.liftQ f h) = (q.comap f).map (mkQ p)
  证明: le_antisymm (by rintro ⟨x⟩ hx; exact ⟨_, hx, rfl⟩)
    (by rw [map_le_iff_le_comap, ← comap_comp, liftQ_mkQ])

Depends on / 依赖: comap_comp, le_antisymm, liftQ_mkQ, map_le_iff_le_comap
-/
theorem comap_liftQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : q.comap (p.liftQ f h) = (q.comap f).map (mkQ p) :=
  le_antisymm (by rintro ⟨x⟩ hx; exact ⟨_, hx, rfl⟩)
    (by rw [map_le_iff_le_comap, ← comap_comp, liftQ_mkQ])

/--
theorem `map_liftQ` / 定理 `map_liftQ`

English:
theorem map_liftQ
  given: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (h) (q : Submodule R (M ⧸ p))
  proof: le_antisymm (by rintro _ ⟨⟨x⟩, hxq, rfl⟩; exact ⟨x, hxq, rfl⟩)
    (by rintro _ ⟨x, hxq, rfl⟩; exact ⟨Quotient.mk x, hxq, rfl⟩)

中文:
定理 map_liftQ
  条件: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (h) (q : 子模 R (M ⧸ p))
  证明: le_antisymm (by rintro _ ⟨⟨x⟩, hxq, rfl⟩; exact ⟨x, hxq, rfl⟩)
    (by rintro _ ⟨x, hxq, rfl⟩; exact ⟨Quotient.mk x, hxq, rfl⟩)

Depends on / 依赖: Quotient, Quotient.mk, le_antisymm
-/
theorem map_liftQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (h) (q : Submodule R (M ⧸ p)) :
    q.map (p.liftQ f h) = (q.comap p.mkQ).map f :=
  le_antisymm (by rintro _ ⟨⟨x⟩, hxq, rfl⟩; exact ⟨x, hxq, rfl⟩)
    (by rintro _ ⟨x, hxq, rfl⟩; exact ⟨Quotient.mk x, hxq, rfl⟩)

/--
theorem `ker_liftQ` / 定理 `ker_liftQ`

English:
theorem ker_liftQ
  given: (f : M ->ₛₗ[τ₁₂] M₂) (h)
  statement: ker (p.liftQ f h) = (ker f).map (mkQ p)
  proof: comap_liftQ _ _ _ _

中文:
定理 ker_liftQ
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (h)
  结论: ker (p.liftQ f h) = (ker f).map (mkQ p)
  证明: comap_liftQ _ _ _ _

Depends on / 依赖: comap_liftQ
-/
theorem ker_liftQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : ker (p.liftQ f h) = (ker f).map (mkQ p) :=
  comap_liftQ _ _ _ _

/--
lemma `ker_mapQ` / 引理 `ker_mapQ`

English:
lemma ker_mapQ
  given: (f : M ->ₛₗ[τ₁₂] M₂) (h)
  statement: ker (p.mapQ q f h) = (comap f q).map p.mkQ
  proof: by
  simp [Submodule.mapQ, Submodule.ker_liftQ, LinearMap.ker_comp]

中文:
引理 ker_mapQ
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (h)
  结论: ker (p.mapQ q f h) = (comap f q).map p.mkQ
  证明: by
  simp [Submodule.mapQ, Submodule.ker_liftQ, LinearMap.ker_comp]

Depends on / 依赖: LinearMap, LinearMap.ker_comp, Submodule, Submodule.ker_liftQ, Submodule.mapQ, ker_comp, ker_liftQ
-/
lemma ker_mapQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : ker (p.mapQ q f h) = (comap f q).map p.mkQ := by
  simp [Submodule.mapQ, Submodule.ker_liftQ, LinearMap.ker_comp]

/--
theorem `range_liftQ` / 定理 `range_liftQ`

English:
theorem range_liftQ
  given: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (h)
  proof: by simpa only [range_eq_map] using! map_liftQ _ _ _ _

中文:
定理 range_liftQ
  条件: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (h)
  证明: by simpa only [range_eq_map] using! map_liftQ _ _ _ _

Depends on / 依赖: map_liftQ, range_eq_map
-/
theorem range_liftQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (h) :
    range (p.liftQ f h) = range f := by simpa only [range_eq_map] using! map_liftQ _ _ _ _

/--
theorem `ker_liftQ_eq_bot` / 定理 `ker_liftQ_eq_bot`

English:
theorem ker_liftQ_eq_bot
  given: (f : M ->ₛₗ[τ₁₂] M₂) (h) (h' : ker f <= p)
  statement: ker (p.liftQ f h) = ⊥
  proof: by
  rw [ker_liftQ]; rw [le_antisymm h h']; rw [mkQ_map_self]

中文:
定理 ker_liftQ_eq_bot
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (h) (h' : ker f <= p)
  结论: ker (p.liftQ f h) = ⊥
  证明: by
  rw [ker_liftQ]; rw [le_antisymm h h']; rw [mkQ_map_self]

Depends on / 依赖: ker_liftQ, le_antisymm, mkQ_map_self
-/
theorem ker_liftQ_eq_bot (f : M ->ₛₗ[τ₁₂] M₂) (h) (h' : ker f <= p) : ker (p.liftQ f h) = ⊥ := by
  rw [ker_liftQ]; rw [le_antisymm h h']; rw [mkQ_map_self]

/--
theorem `ker_liftQ_eq_bot'` / 定理 `ker_liftQ_eq_bot'`

English:
theorem ker_liftQ_eq_bot'
  given: (f : M ->ₛₗ[τ₁₂] M₂) (h : p = ker f)
  proof: ker_liftQ_eq_bot p f h.le h.ge

中文:
定理 ker_liftQ_eq_bot'
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (h : p = ker f)
  证明: ker_liftQ_eq_bot p f h.le h.ge

Depends on / 依赖: h.ge, h.le, ker_liftQ_eq_bot
-/
theorem ker_liftQ_eq_bot' (f : M ->ₛₗ[τ₁₂] M₂) (h : p = ker f) :
    ker (p.liftQ f (le_of_eq h)) = ⊥ :=
  ker_liftQ_eq_bot p f h.le h.ge

/--
theorem `range_mapQ` / 定理 `range_mapQ`

English:
theorem range_mapQ
  given: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (h : p <= comap f q)
  proof: by
  rw [mapQ]; rw [range_liftQ]; rw [range_comp]

中文:
定理 range_mapQ
  条件: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (h : p <= comap f q)
  证明: by
  rw [mapQ]; rw [range_liftQ]; rw [range_comp]

Depends on / 依赖: range_comp, range_liftQ
-/
theorem range_mapQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (h : p <= comap f q) :
    (p.mapQ q f h).range = f.range.map q.mkQ := by
  rw [mapQ]; rw [range_liftQ]; rw [range_comp]

section

variable {p p' p''}

/--
Definition of `factor` / `factor` 的定义

English:
abbreviation factor
  signature: (H : p <= p')
  body: mapQ _ _ LinearMap.id H

@[simp]

中文:
缩写 factor
  签名: (H : p <= p')
  定义体: mapQ _ _ LinearMap.id H

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id
-/
abbrev factor (H : p <= p') : M ⧸ p ->ₗ[R] M ⧸ p' :=
  mapQ _ _ LinearMap.id H

@[simp]
/--
theorem `factor_mk` / 定理 `factor_mk`

English:
theorem factor_mk
  given: (H : p <= p') (x : M)
  statement: factor H (mkQ p x) = mkQ p' x
  proof: rfl

@[simp]

中文:
定理 factor_mk
  条件: (H : p <= p') (x : M)
  结论: factor H (mkQ p x) = mkQ p' x
  证明: rfl

@[simp]
-/
theorem factor_mk (H : p <= p') (x : M) : factor H (mkQ p x) = mkQ p' x :=
  rfl

@[simp]
/--
theorem `factor_comp_mk` / 定理 `factor_comp_mk`

English:
theorem factor_comp_mk
  given: (H : p <= p')
  statement: (factor H).comp (mkQ p) = mkQ p'
  proof: by
  ext x
  rw [LinearMap.comp_apply]; rw [factor_mk]

中文:
定理 factor_comp_mk
  条件: (H : p <= p')
  结论: (factor H).comp (mkQ p) = mkQ p'
  证明: by
  ext x
  rw [LinearMap.comp_apply]; rw [factor_mk]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, comp_apply, factor_mk
-/
theorem factor_comp_mk (H : p <= p') : (factor H).comp (mkQ p) = mkQ p' := by
  ext x
  rw [LinearMap.comp_apply]; rw [factor_mk]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `factor_comp` / 定理 `factor_comp`

English:
theorem factor_comp
  given: (H1 : p <= p') (H2 : p' <= p'')
  proof: by
  ext
  simp

@[simp]

中文:
定理 factor_comp
  条件: (H1 : p <= p') (H2 : p' <= p'')
  证明: by
  ext
  simp

@[simp]
-/
theorem factor_comp (H1 : p <= p') (H2 : p' <= p'') :
    (factor H2).comp (factor H1) = factor (H1.trans H2) := by
  ext
  simp

@[simp]
/--
theorem `factor_comp_apply` / 定理 `factor_comp_apply`

English:
theorem factor_comp_apply
  given: (H1 : p <= p') (H2 : p' <= p'') (x : M ⧸ p)
  proof: by
  rw [← comp_apply]
  simp

中文:
定理 factor_comp_apply
  条件: (H1 : p <= p') (H2 : p' <= p'') (x : M ⧸ p)
  证明: by
  rw [← comp_apply]
  simp

Depends on / 依赖: comp_apply
-/
theorem factor_comp_apply (H1 : p <= p') (H2 : p' <= p'') (x : M ⧸ p) :
    factor H2 (factor H1 x) = factor (H1.trans H2) x := by
  rw [← comp_apply]
  simp

/--
lemma `factor_surjective` / 引理 `factor_surjective`

English:
lemma factor_surjective
  given: (H : p <= p')
  statement: Function.Surjective (factor H)
  proof: by
  intro x
  use Quotient.mk x.out
  exact Quotient.out_eq x

中文:
引理 factor_surjective
  条件: (H : p <= p')
  结论: 函数.满射 (factor H)
  证明: by
  intro x
  use Quotient.mk x.out
  exact Quotient.out_eq x

Depends on / 依赖: Quotient, Quotient.mk, Quotient.out_eq, out_eq, x.out
-/
lemma factor_surjective (H : p <= p') : Function.Surjective (factor H) := by
  intro x
  use Quotient.mk x.out
  exact Quotient.out_eq x

end

/--
Definition of `comapMkQRelIso` / `comapMkQRelIso` 的定义

English:
definition comapMkQRelIso
  signature: : Submodule R (M ⧸ p) ≃o Set.Ici p where
  body: ⟨comap p.mkQ p', le_comap_mkQ p _⟩
  invFun q := map p.mkQ q
left_inv p' := map_comap_eq_self by simp
right_inv := fun ⟨q, hq⟩ => Subtype.ext by simpa [comap_map_mkQ p]
map_rel_iff' := comap_le_comap_iff range_mkQ _

中文:
定义 comapMkQRelIso
  签名: : 子模 R (M ⧸ p) ≃o 集合.左闭右无界区间 p where
  定义体: ⟨comap p.mkQ p', le_comap_mkQ p _⟩
  invFun q := map p.mkQ q
left_inv p' := map_comap_eq_self by simp
right_inv := fun ⟨q, hq⟩ => Subtype.ext by simpa [comap_map_mkQ p]
map_rel_iff' := comap_le_comap_iff range_mkQ _

Depends on / 依赖: le_comap_mkQ, p.mkQ
-/
def comapMkQRelIso : Submodule R (M ⧸ p) ≃o Set.Ici p where
  toFun p' := ⟨comap p.mkQ p', le_comap_mkQ p _⟩
  invFun q := map p.mkQ q
left_inv p' := map_comap_eq_self by simp
right_inv := fun ⟨q, hq⟩ => Subtype.ext by simpa [comap_map_mkQ p]
map_rel_iff' := comap_le_comap_iff range_mkQ _

/--
Definition of `comapMkQOrderEmbedding` / `comapMkQOrderEmbedding` 的定义

English:
definition comapMkQOrderEmbedding
  signature: : Submodule R (M ⧸ p) ↪o Submodule R M
  body: (RelIso.toRelEmbedding <| comapMkQRelIso p).trans (Subtype.relEmbedding (· <= ·) _)

@[simp]

中文:
定义 comapMkQOrderEmbedding
  签名: : 子模 R (M ⧸ p) ↪o 子模 R M
  定义体: (RelIso.toRelEmbedding <| comapMkQRelIso p).trans (Subtype.relEmbedding (· <= ·) _)

@[simp]

Depends on / 依赖: RelIso, RelIso.toRelEmbedding, Subtype, Subtype.relEmbedding, comapMkQRelIso, relEmbedding, toRelEmbedding
-/
def comapMkQOrderEmbedding : Submodule R (M ⧸ p) ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| comapMkQRelIso p).trans (Subtype.relEmbedding (· <= ·) _)

@[simp]
/--
theorem `comapMkQOrderEmbedding_eq` / 定理 `comapMkQOrderEmbedding_eq`

English:
theorem comapMkQOrderEmbedding_eq
  given: (p' : Submodule R (M ⧸ p))
  proof: rfl

中文:
定理 comapMkQOrderEmbedding_eq
  条件: (p' : 子模 R (M ⧸ p))
  证明: rfl
-/
theorem comapMkQOrderEmbedding_eq (p' : Submodule R (M ⧸ p)) :
    comapMkQOrderEmbedding p p' = comap p.mkQ p' :=
  rfl

/--
theorem `span_preimage_eq` / 定理 `span_preimage_eq`

English:
theorem span_preimage_eq
  statement: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {s : Set M₂} (h₀ : s.Nonempty)
  proof: by
  suffices (span R₂ s).comap f <= span R (f ⁻¹' s) by exact le_antisymm (span_preimage_le f s) this
  have hk : ker f <= span R (f ⁻¹' s) := by
    let y := Classical.choose h₀
    have hy : y in s := Classical.choose_spec h₀
    rw [ker_le_iff]
    use y, h₁ hy
    rw [← Set.singleton_subset_iff

中文:
定理 span_preimage_eq
  结论: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {s : 集合 M₂} (h₀ : s.非空)
  证明: by
  suffices (span R₂ s).comap f <= span R (f ⁻¹' s) by exact le_antisymm (span_preimage_le f s) this
  have hk : ker f <= span R (f ⁻¹' s) := by
    let y := Classical.choose h₀
    have hy : y in s := Classical.choose_spec h₀
    rw [ker_le_iff]
    use y, h₁ hy
    rw [← Set.singleton_subset_iff

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, LinearMap, LinearMap.map_le_map_iff, Set.Subset.trans, Set.image_preimage, Set.preimage_mono, Set.singleton_subset_iff, Subset, choose_spec, coe_range, image_preimage, ker_le_iff, le_antisymm, left_eq_sup, map_comap_eq, map_le_map_iff, map_span, preimage_mono
-/
theorem span_preimage_eq [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {s : Set M₂} (h₀ : s.Nonempty)
    (h₁ : s subseteq range f) : span R (f ⁻¹' s) = (span R₂ s).comap f := by
  suffices (span R₂ s).comap f <= span R (f ⁻¹' s) by exact le_antisymm (span_preimage_le f s) this
  have hk : ker f <= span R (f ⁻¹' s) := by
    let y := Classical.choose h₀
    have hy : y in s := Classical.choose_spec h₀
    rw [ker_le_iff]
    use y, h₁ hy
    rw [← Set.singleton_subset_iff] at hy
    exact Set.Subset.trans subset_span (span_mono (Set.preimage_mono hy))
  rw [← left_eq_sup] at hk
  rw [coe_range f] at h₁
  rw [hk]; rw [← LinearMap.map_le_map_iff]; rw [map_span]; rw [map_comap_eq]; rw [Set.image_preimage_eq_of_subset h₁]
  exact inf_le_right

variable {R₂ : Type*} [Ring R₂] {σ₁₂ : R ->+* R₂} {σ₂₁ : R₂ ->+* R}
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R₂ N]
  (P : Submodule R M) (Q : Submodule R₂ N)

/--
Definition of `Quotient.equiv` / `Quotient.equiv` 的定义

English:
definition Quotient.equiv
  signature: (f : M ≃ₛₗ[σ₁₂] N) (hf : P.map (f : M ->ₛₗ[σ₁₂] N) = Q)
  body: P.mapQ Q (f : M ->ₛₗ[σ₁₂] N) (map_le_iff_le_comap.mp hf.le)
  invFun := Q.mapQ P (f.symm : N ->ₛₗ[σ₂₁] M) (hf.symm.trans (map_equiv_eq_comap_symm f _)).le
  left_inv x := Quotient.induction_on _ x (by simp)
  right_inv x := Quotient.induction_on _ x (by simp)

@[simp]

中文:
定义 商.equiv
  签名: (f : M ≃ₛₗ[σ₁₂] N) (hf : P.map (f : M ->ₛₗ[σ₁₂] N) = Q)
  定义体: P.mapQ Q (f : M ->ₛₗ[σ₁₂] N) (map_le_iff_le_comap.mp hf.le)
  invFun := Q.mapQ P (f.symm : N ->ₛₗ[σ₂₁] M) (hf.symm.trans (map_equiv_eq_comap_symm f _)).le
  left_inv x := Quotient.induction_on _ x (by simp)
  right_inv x := Quotient.induction_on _ x (by simp)

@[simp]

Depends on / 依赖: P.mapQ, hf.le, map_le_iff_le_comap, map_le_iff_le_comap.mp
-/
def Quotient.equiv (f : M ≃ₛₗ[σ₁₂] N) (hf : P.map (f : M ->ₛₗ[σ₁₂] N) = Q) :
    (M ⧸ P) ≃ₛₗ[σ₁₂] N ⧸ Q where
  __ := P.mapQ Q (f : M ->ₛₗ[σ₁₂] N) (map_le_iff_le_comap.mp hf.le)
  invFun := Q.mapQ P (f.symm : N ->ₛₗ[σ₂₁] M) (hf.symm.trans (map_equiv_eq_comap_symm f _)).le
  left_inv x := Quotient.induction_on _ x (by simp)
  right_inv x := Quotient.induction_on _ x (by simp)

@[simp]
/--
lemma `Quotient.equiv_apply` / 引理 `Quotient.equiv_apply`

English:
lemma Quotient.equiv_apply
  given: (f : M ≃ₛₗ[σ₁₂] N) (hf : P.map (f : M ->ₛₗ[σ₁₂] N) = Q) (a : M ⧸ P)
  proof: rfl

@[simp]

中文:
引理 商.equiv_apply
  条件: (f : M ≃ₛₗ[σ₁₂] N) (hf : P.map (f : M ->ₛₗ[σ₁₂] N) = Q) (a : M ⧸ P)
  证明: rfl

@[simp]
-/
lemma Quotient.equiv_apply (f : M ≃ₛₗ[σ₁₂] N) (hf : P.map (f : M ->ₛₗ[σ₁₂] N) = Q) (a : M ⧸ P) :
    equiv P Q f hf a = P.mapQ Q (f : M ->ₛₗ[σ₁₂] N) (map_le_iff_le_comap.mp hf.le) a :=
  rfl

@[simp]
/--
lemma `Quotient.equiv_symm` / 引理 `Quotient.equiv_symm`

English:
lemma Quotient.equiv_symm
  given: (f : M ≃ₛₗ[σ₁₂] N) (hf : P.map (f : M ->ₛₗ[σ₁₂] N) = Q)
  proof: rfl

@[simp]

中文:
引理 商.equiv_symm
  条件: (f : M ≃ₛₗ[σ₁₂] N) (hf : P.map (f : M ->ₛₗ[σ₁₂] N) = Q)
  证明: rfl

@[simp]
-/
lemma Quotient.equiv_symm (f : M ≃ₛₗ[σ₁₂] N) (hf : P.map (f : M ->ₛₗ[σ₁₂] N) = Q) :
    (Quotient.equiv P Q f hf).symm = Quotient.equiv Q P f.symm ((map_symm_eq_iff f).mpr hf) :=
  rfl

@[simp]
/--
theorem `Quotient.equiv_trans` / 定理 `Quotient.equiv_trans`

English:
theorem Quotient.equiv_trans
  statement: {R₃ : Type*} {O : Type*} [Ring R₃] [AddCommGroup O] [Module R₃ O]
  proof: by
  ext
  -- `simp` can deal with `hef` depending on `e` and `f`
  simp only [Quotient.equiv_apply, LinearEquiv.trans_apply, LinearEquiv.coe_trans]
  -- `rw` can deal with `mapQ_comp` needing extra hypotheses coming from the RHS
  rw [mapQ_comp]; rw [LinearMap.comp_apply]

中文:
定理 商.equiv_trans
  结论: {R₃ : 类型} {O : 类型} [环 R₃] [加法交换群 O] [模 R₃ O]
  证明: by
  ext
  -- `simp` can deal with `hef` depending on `e` and `f`
  simp only [Quotient.equiv_apply, LinearEquiv.trans_apply, LinearEquiv.coe_trans]
  -- `rw` can deal with `mapQ_comp` needing extra hypotheses coming from the RHS
  rw [mapQ_comp]; rw [LinearMap.comp_apply]
-/
theorem Quotient.equiv_trans {R₃ : Type*} {O : Type*} [Ring R₃] [AddCommGroup O] [Module R₃ O]
    {σ₂₃ : R₂ ->+* R₃} {σ₃₂ : R₃ ->+* R₂} {σ₁₃ : R ->+* R₃} {σ₃₁ : R₃ ->+* R}
    [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
    [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
    (S : Submodule R₃ O) (e : M ≃ₛₗ[σ₁₂] N) (f : N ≃ₛₗ[σ₂₃] O)
    (he : P.map (e : M ->ₛₗ[σ₁₂] N) = Q) (hf : Q.map (f : N ->ₛₗ[σ₂₃] O) = S)
    (hef : P.map ((e.trans f : M ≃ₛₗ[σ₁₃] O) : M ->ₛₗ[σ₁₃] O) = S) :
    Quotient.equiv P S (e.trans f) hef =
      (Quotient.equiv P Q e he).trans (Quotient.equiv Q S f hf) := by
  ext
  -- `simp` can deal with `hef` depending on `e` and `f`
  simp only [Quotient.equiv_apply, LinearEquiv.trans_apply, LinearEquiv.coe_trans]
  -- `rw` can deal with `mapQ_comp` needing extra hypotheses coming from the RHS
  rw [mapQ_comp]; rw [LinearMap.comp_apply]

end Submodule

open Submodule

namespace LinearMap

section Ring

variable {R M R₂ M₂ R₃ M₃ : Type*}
variable [Ring R] [Ring R₂] [Ring R₃]
variable [AddCommMonoid M] [AddCommGroup M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {τ₁₂ : R ->+* R₂} {τ₂₃ : R₂ ->+* R₃} {τ₁₃ : R ->+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃] [RingHomSurjective τ₁₂]

/--
theorem `range_mkQ_comp` / 定理 `range_mkQ_comp`

English:
theorem range_mkQ_comp
  given: (f : M ->ₛₗ[τ₁₂] M₂)
  statement: (range f).mkQ.comp f = 0
  proof: LinearMap.ext fun x => by simp

中文:
定理 range_mkQ_comp
  条件: (f : M ->ₛₗ[τ₁₂] M₂)
  结论: (range f).mkQ.comp f = 0
  证明: LinearMap.ext fun x => by simp

Depends on / 依赖: LinearMap, LinearMap.ext
-/
theorem range_mkQ_comp (f : M ->ₛₗ[τ₁₂] M₂) : (range f).mkQ.comp f = 0 :=
  LinearMap.ext fun x => by simp

/--
theorem `ker_le_range_iff` / 定理 `ker_le_range_iff`

English:
theorem ker_le_range_iff
  given: {f : M ->ₛₗ[τ₁₂] M₂} {g : M₂ ->ₛₗ[τ₂₃] M₃}
  proof: by
  rw [← range_le_ker_iff]; rw [Submodule.ker_mkQ]; rw [Submodule.range_subtype]

中文:
定理 ker_le_range_iff
  条件: {f : M ->ₛₗ[τ₁₂] M₂} {g : M₂ ->ₛₗ[τ₂₃] M₃}
  证明: by
  rw [← range_le_ker_iff]; rw [Submodule.ker_mkQ]; rw [Submodule.range_subtype]

Depends on / 依赖: Submodule, Submodule.ker_mkQ, Submodule.range_subtype, ker_mkQ, range_le_ker_iff, range_subtype
-/
theorem ker_le_range_iff {f : M ->ₛₗ[τ₁₂] M₂} {g : M₂ ->ₛₗ[τ₂₃] M₃} :
    ker g <= range f ↔ (range f).mkQ.comp (ker g).subtype = 0 := by
  rw [← range_le_ker_iff]; rw [Submodule.ker_mkQ]; rw [Submodule.range_subtype]

/--
theorem `range_eq_top_of_cancel` / 定理 `range_eq_top_of_cancel`

English:
theorem range_eq_top_of_cancel
  statement: {f : M ->ₛₗ[τ₁₂] M₂}
  proof: by
  have h₁ : (0 : M₂ ->ₗ[R₂] M₂ ⧸ (range f)).comp f = 0 := zero_comp _
  rw [← Submodule.ker_mkQ (range f)]; rw [← h 0 (range f).mkQ (Eq.trans h₁ (range_mkQ_comp _).symm)]
  exact ker_zero

中文:
定理 range_eq_top_of_cancel
  结论: {f : M ->ₛₗ[τ₁₂] M₂}
  证明: by
  have h₁ : (0 : M₂ ->ₗ[R₂] M₂ ⧸ (range f)).comp f = 0 := zero_comp _
  rw [← Submodule.ker_mkQ (range f)]; rw [← h 0 (range f).mkQ (Eq.trans h₁ (range_mkQ_comp _).symm)]
  exact ker_zero

Depends on / 依赖: Eq.trans, Submodule, Submodule.ker_mkQ, ker_mkQ, ker_zero, range_mkQ_comp, zero_comp
-/
theorem range_eq_top_of_cancel {f : M ->ₛₗ[τ₁₂] M₂}
    (h : forall u v : M₂ ->ₗ[R₂] M₂ ⧸ (range f), u.comp f = v.comp f -> u = v) : range f = ⊤ := by
  have h₁ : (0 : M₂ ->ₗ[R₂] M₂ ⧸ (range f)).comp f = 0 := zero_comp _
  rw [← Submodule.ker_mkQ (range f)]; rw [← h 0 (range f).mkQ (Eq.trans h₁ (range_mkQ_comp _).symm)]
  exact ker_zero

end Ring

end LinearMap

open LinearMap

namespace Submodule

variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]
variable (p p' : Submodule R M)

/--
Definition of `quotEquivOfEqBot` / `quotEquivOfEqBot` 的定义

English:
definition quotEquivOfEqBot
  signature: (hp : p = ⊥)
  body: LinearEquiv.ofLinearMap (p.liftQ id <| hp.symm ▸ bot_le) p.mkQ (liftQ_mkQ _ _ _)
    p.quot_hom_ext _ LinearMap.id fun _ => rfl

@[simp]

中文:
定义 quotEquivOfEqBot
  签名: (hp : p = ⊥)
  定义体: LinearEquiv.ofLinearMap (p.liftQ id <| hp.symm ▸ bot_le) p.mkQ (liftQ_mkQ _ _ _)
    p.quot_hom_ext _ LinearMap.id fun _ => rfl

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.id, bot_le, hp.symm, liftQ_mkQ, ofLinearMap, p.liftQ, p.mkQ, p.quot_hom_ext, quot_hom_ext
-/
def quotEquivOfEqBot (hp : p = ⊥) : (M ⧸ p) ≃ₗ[R] M :=
LinearEquiv.ofLinearMap (p.liftQ id <| hp.symm ▸ bot_le) p.mkQ (liftQ_mkQ _ _ _)
    p.quot_hom_ext _ LinearMap.id fun _ => rfl

@[simp]
/--
theorem `quotEquivOfEqBot_apply_mk` / 定理 `quotEquivOfEqBot_apply_mk`

English:
theorem quotEquivOfEqBot_apply_mk
  given: (hp : p = ⊥) (x : M)
  proof: rfl

@[simp]

中文:
定理 quotEquivOfEqBot_apply_mk
  条件: (hp : p = ⊥) (x : M)
  证明: rfl

@[simp]
-/
theorem quotEquivOfEqBot_apply_mk (hp : p = ⊥) (x : M) :
    p.quotEquivOfEqBot hp (Quotient.mk x) = x :=
  rfl

@[simp]
/--
theorem `quotEquivOfEqBot_symm_apply` / 定理 `quotEquivOfEqBot_symm_apply`

English:
theorem quotEquivOfEqBot_symm_apply
  given: (hp : p = ⊥) (x : M)
  proof: rfl

@[simp]

中文:
定理 quotEquivOfEqBot_symm_apply
  条件: (hp : p = ⊥) (x : M)
  证明: rfl

@[simp]
-/
theorem quotEquivOfEqBot_symm_apply (hp : p = ⊥) (x : M) :
    (p.quotEquivOfEqBot hp).symm x = (Quotient.mk x) :=
  rfl

@[simp]
/--
theorem `coe_quotEquivOfEqBot_symm` / 定理 `coe_quotEquivOfEqBot_symm`

English:
theorem coe_quotEquivOfEqBot_symm
  given: (hp : p = ⊥)
  proof: rfl

@[simp]

中文:
定理 coe_quotEquivOfEqBot_symm
  条件: (hp : p = ⊥)
  证明: rfl

@[simp]
-/
theorem coe_quotEquivOfEqBot_symm (hp : p = ⊥) :
    ((p.quotEquivOfEqBot hp).symm : M ->ₗ[R] M ⧸ p) = p.mkQ :=
  rfl

@[simp]
/--
theorem `Quotient.equiv_refl` / 定理 `Quotient.equiv_refl`

English:
theorem Quotient.equiv_refl
  statement: (P : Submodule R M) (Q : Submodule R M)
  proof: rfl

中文:
定理 商.equiv_refl
  结论: (P : 子模 R M) (Q : 子模 R M)
  证明: rfl
-/
theorem Quotient.equiv_refl (P : Submodule R M) (Q : Submodule R M)
    (hf : P.map (LinearEquiv.refl R M : M ->ₗ[R] M) = Q) :
    Quotient.equiv P Q (LinearEquiv.refl R M) hf = quotEquivOfEq _ _ (by simpa using hf) :=
  rfl

end Submodule

end Ring

section CommRing

variable {R M M₂ : Type*} {r : R} {x y : M} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M₂] [Module R M₂] (p : Submodule R M) (q : Submodule R M₂)

namespace Submodule

/--
Definition of `mapQLinear` / `mapQLinear` 的定义

English:
definition mapQLinear
  signature: : compatibleMaps p q ->ₗ[R] M ⧸ p ->ₗ[R] M₂ ⧸ q where
  body: mapQ _ _ f.val f.property
  map_add' x y := by
    ext
    rfl
  map_smul' c f := by
    ext
    rfl

中文:
定义 mapQLinear
  签名: : compatibleMaps p q ->ₗ[R] M ⧸ p ->ₗ[R] M₂ ⧸ q where
  定义体: mapQ _ _ f.val f.property
  map_add' x y := by
    ext
    rfl
  map_smul' c f := by
    ext
    rfl

Depends on / 依赖: f.property, f.val, property
-/
def mapQLinear : compatibleMaps p q ->ₗ[R] M ⧸ p ->ₗ[R] M₂ ⧸ q where
  toFun f := mapQ _ _ f.val f.property
  map_add' x y := by
    ext
    rfl
  map_smul' c f := by
    ext
    rfl

end Submodule

end CommRing
