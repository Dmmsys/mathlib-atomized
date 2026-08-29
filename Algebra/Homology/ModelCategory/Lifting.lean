/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Lifting properties in cochain complexes

Let `C` be an abelian category. Consider a commutative diagram
in the category `CochainComplex C ℤ`.
```
   t
 A ⟶ X
i| |p
 v v
 B ⟶ Y
   b
```
Assume that there exists a degreewise lifting `B.X n ⟶ X.X n` for any `n : ℤ`,
that `Q` is a cokernel of `i`, and `K` is a kernel of `p`. In this situation,
we construct a cocycle in `Cocycle Q K 1` and show that there exists
a lifting `B ⟶ X` if this cocycle is a coboundary.

-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Limits HomComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace Lifting

variable {A B X Y : CochainComplex C Int}
  {t : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {b : B ⟶ Y}
  (sq : CommSq t i p b)
  (hsq : forall n, (sq.map (HomologicalComplex.eval _ _ n)).LiftStruct)
  {Q : CochainComplex C Int} {π : B ⟶ Q} {hπ : i ≫ π = 0}
  (hQ : IsColimit (CokernelCofork.ofπ _ hπ))
  {K : CochainComplex C Int} {ι : K ⟶ X} {hι : ι ≫ p = 0}
  (hK : IsLimit (KernelFork.ofι _ hι))

/--
Definition of `cochain₀` / `cochain₀` 的定义

English:
abbreviation cochain₀
  signature: : Cochain B X 0
  body: Cochain.ofHoms (fun n => (hsq n).l)

中文:
缩写 cochain₀
  签名: : Cochain B X 0
  定义体: Cochain.ofHoms (fun n => (hsq n).l)

Depends on / 依赖: Cochain, Cochain.ofHoms, ofHoms
-/
abbrev cochain₀ : Cochain B X 0 := Cochain.ofHoms (fun n => (hsq n).l)

/--
Definition of `cocycle₁'` / `cocycle₁'` 的定义

English:
definition cocycle₁'
  signature: : Cocycle B X 1
  body: Cocycle.mk (δ 0 1 (cochain₀ sq hsq)) 2 (by simp) (by simp [δ_δ])

中文:
定义 cocycle₁'
  签名: : Cocycle B X 1
  定义体: Cocycle.mk (δ 0 1 (cochain₀ sq hsq)) 2 (by simp) (by simp [δ_δ])

Depends on / 依赖: Cocycle, Cocycle.mk
-/
def cocycle₁' : Cocycle B X 1 :=
  Cocycle.mk (δ 0 1 (cochain₀ sq hsq)) 2 (by simp) (by simp [δ_δ])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `coe_cocycle₁'_v_comp_eq_zero` / 引理 `coe_cocycle₁'_v_comp_eq_zero`

English:
lemma coe_cocycle₁'_v_comp_eq_zero
  given: (n m : Int) (hnm : n + 1 = m := by lia)
  proof: by
  have fac_right (k : Int) := (hsq k).fac_right
  dsimp at fac_right
  simp [cocycle₁', -HomologicalComplex.Hom.comm,
    ← p.comm, fac_right, reassoc_of% fac_right, b.comm]

中文:
引理 coe_cocycle₁'_v_comp_eq_zero
  条件: (n m : 整数) (hnm : n + 1 = m := by lia)
  证明: by
  have fac_right (k : Int) := (hsq k).fac_right
  dsimp at fac_right
  simp [cocycle₁', -HomologicalComplex.Hom.comm,
    ← p.comm, fac_right, reassoc_of% fac_right, b.comm]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.comm, b.comm, fac_right, p.comm, reassoc_of
-/
lemma coe_cocycle₁'_v_comp_eq_zero (n m : Int) (hnm : n + 1 = m := by lia) :
    (cocycle₁' sq hsq).1.v n m hnm ≫ p.f m = 0 := by
  have fac_right (k : Int) := (hsq k).fac_right
  dsimp at fac_right
  simp [cocycle₁', -HomologicalComplex.Hom.comm,
    ← p.comm, fac_right, reassoc_of% fac_right, b.comm]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `comp_coe_cocyle₁'_v_eq_zero` / 引理 `comp_coe_cocyle₁'_v_eq_zero`

English:
lemma comp_coe_cocyle₁'_v_eq_zero
  given: (n m : Int) (hnm : n + 1 = m := by lia)
  proof: by
  have fac_left (k : Int) := (hsq k).fac_left
  dsimp at fac_left
  simp [cocycle₁', fac_left, reassoc_of% fac_left]

中文:
引理 comp_coe_cocyle₁'_v_eq_zero
  条件: (n m : 整数) (hnm : n + 1 = m := by lia)
  证明: by
  have fac_left (k : Int) := (hsq k).fac_left
  dsimp at fac_left
  simp [cocycle₁', fac_left, reassoc_of% fac_left]

Depends on / 依赖: fac_left, reassoc_of
-/
lemma comp_coe_cocyle₁'_v_eq_zero (n m : Int) (hnm : n + 1 = m := by lia) :
    i.f n ≫ (cocycle₁' sq hsq).1.v n m hnm = 0 := by
  have fac_left (k : Int) := (hsq k).fac_left
  dsimp at fac_left
  simp [cocycle₁', fac_left, reassoc_of% fac_left]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hQ hK in
/--
lemma `exists_hom` / 引理 `exists_hom`

English:
lemma exists_hom
  given: (n m : Int) (hnm : n + 1 = m := by lia)
  proof: by
  have : Epi π := Cofork.IsColimit.epi hQ
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc'
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).1
    (isColimitOfPreserves (HomologicalComplex.eval _ _ n) hQ))
    ((cocycle₁' sq hsq).1.v n m hnm) (by simp)
  dsimp [CokernelCofork.map] at l hl
  obtain ⟨l', hl'⟩ := KernelFork.IsLimit.lift' ((KernelFork.isLimitMapConeEquiv _ _).1
    (isLimitOfPreserves (HomologicalComplex.eval _ _ m) hK)) l (by
      simp [← cancel_epi (π.f n), reassoc_of% hl])
  exact ⟨l', by cat_disch⟩

中文:
引理 存在_hom
  条件: (n m : 整数) (hnm : n + 1 = m := by lia)
  证明: by
  have : Epi π := Cofork.IsColimit.epi hQ
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc'
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).1
    (isColimitOfPreserves (HomologicalComplex.eval _ _ n) hQ))
    ((cocycle₁' sq hsq).1.v n m hnm) (by simp)
  dsimp [CokernelCofork.map] at l hl
  obtain ⟨l', hl'⟩ := KernelFork.IsLimit.lift' ((KernelFork.isLimitMapConeEquiv _ _).1
    (isLimitOfPreserves (HomologicalComplex.eval _ _ m) hK)) l (by
      simp [← cancel_epi (π.f n), reassoc_of% hl])
  exact ⟨l', by cat_disch⟩

Depends on / 依赖: Cofork, Cofork.IsColimit.epi, CokernelCofork, CokernelCofork.IsColimit.desc, CokernelCofork.isColimitMapCoconeEquiv, CokernelCofork.map, HomologicalComplex, HomologicalComplex.eval, IsColimit, IsLimit, KernelFork, KernelFork.IsLimit.lift, KernelFork.isLimitMapConeEquiv, isColimitMapCoconeEquiv, isColimitOfPreserves, isLimitMapConeEquiv, isLimitOfPreserves
-/
lemma exists_hom (n m : Int) (hnm : n + 1 = m := by lia) :
    exists (φ : Q.X n ⟶ K.X m), π.f n ≫ φ ≫ ι.f m = (cocycle₁' sq hsq).1.v n m hnm := by
  have : Epi π := Cofork.IsColimit.epi hQ
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc'
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).1
    (isColimitOfPreserves (HomologicalComplex.eval _ _ n) hQ))
    ((cocycle₁' sq hsq).1.v n m hnm) (by simp)
  dsimp [CokernelCofork.map] at l hl
  obtain ⟨l', hl'⟩ := KernelFork.IsLimit.lift' ((KernelFork.isLimitMapConeEquiv _ _).1
    (isLimitOfPreserves (HomologicalComplex.eval _ _ m) hK)) l (by
      simp [← cancel_epi (π.f n), reassoc_of% hl])
  exact ⟨l', by cat_disch⟩

/--
Definition of `cochain₁` / `cochain₁` 的定义

English:
definition cochain₁
  signature: : Cochain Q K 1
  body: Cochain.mk (fun n m hnm => (exists_hom sq hsq hQ hK n m hnm).choose)

@[reassoc (attr := simp)]

中文:
定义 cochain₁
  签名: : Cochain Q K 1
  定义体: Cochain.mk (fun n m hnm => (exists_hom sq hsq hQ hK n m hnm).choose)

@[reassoc (attr := simp)]

Depends on / 依赖: Cochain, Cochain.mk, exists_hom
-/
noncomputable def cochain₁ : Cochain Q K 1 :=
  Cochain.mk (fun n m hnm => (exists_hom sq hsq hQ hK n m hnm).choose)

@[reassoc (attr := simp)]
/--
lemma `π_f_cochain₁_v_ι_f` / 引理 `π_f_cochain₁_v_ι_f`

English:
lemma π_f_cochain₁_v_ι_f
  given: (n m : Int) (hnm : n + 1 = m)
  proof: (exists_hom sq hsq hQ hK n m hnm).choose_spec

中文:
引理 π_f_cochain₁_v_ι_f
  条件: (n m : 整数) (hnm : n + 1 = m)
  证明: (exists_hom sq hsq hQ hK n m hnm).choose_spec

Depends on / 依赖: choose_spec, exists_hom
-/
lemma π_f_cochain₁_v_ι_f (n m : Int) (hnm : n + 1 = m) :
    π.f n ≫ (cochain₁ sq hsq hQ hK).v n m hnm ≫ ι.f m = (cocycle₁' sq hsq).1.v n m hnm :=
  (exists_hom sq hsq hQ hK n m hnm).choose_spec

/--
Definition of `cocycle₁` / `cocycle₁` 的定义

English:
definition cocycle₁
  signature: : Cocycle Q K 1
  body: Cocycle.mk (cochain₁ sq hsq hQ hK) 2 (by simp) (by
    have : Epi π := Cofork.IsColimit.epi hQ
    have : Mono ι := Fork.IsLimit.mono hK
    ext n _ rfl
    have := Cochain.congr_v ((cocycle₁' sq hsq).δ_eq_zero 2) n _ rfl
    rw [Cochain.zero_v]; rw [δ_v _ _ (by simp) _ _ _ _ (n + 1) _ (by lia) rfl]; rw [Int.negOnePow_even 2 ⟨1]; rw [by simp⟩]; rw [one_smul] at this ⊢
    rwa [← cancel_mono (ι.f (n + 2)), ← cancel_epi (π.f n),
      Preadditive.add_comp, Category.assoc, Category.assoc, Preadditive.comp_add,
      HomologicalComplex.Hom.comm_assoc,
      π_f_cochain₁_v_ι_f, zero_comp, comp_zero, ← ι.comm,
      π_f_cochain₁_v_ι_f_assoc])

中文:
定义 cocycle₁
  签名: : Cocycle Q K 1
  定义体: Cocycle.mk (cochain₁ sq hsq hQ hK) 2 (by simp) (by
    have : Epi π := Cofork.IsColimit.epi hQ
    have : Mono ι := Fork.IsLimit.mono hK
    ext n _ rfl
    have := Cochain.congr_v ((cocycle₁' sq hsq).δ_eq_zero 2) n _ rfl
    rw [Cochain.zero_v]; rw [δ_v _ _ (by simp) _ _ _ _ (n + 1) _ (by lia) rfl]; rw [Int.negOnePow_even 2 ⟨1]; rw [by simp⟩]; rw [one_smul] at this ⊢
    rwa [← cancel_mono (ι.f (n + 2)), ← cancel_epi (π.f n),
      Preadditive.add_comp, Category.assoc, Category.assoc, Preadditive.comp_add,
      HomologicalComplex.Hom.comm_assoc,
      π_f_cochain₁_v_ι_f, zero_comp, comp_zero, ← ι.comm,
      π_f_cochain₁_v_ι_f_assoc])

Depends on / 依赖: Category, Category.assoc, Cochain, Cochain.congr_v, Cochain.zero_v, Cocycle, Cocycle.mk, Cofork, Cofork.IsColimit.epi, Fork.IsLimit.mono, HomologicalComple, Int.negOnePow_even, IsColimit, IsLimit, Preadditive, Preadditive.add_comp, Preadditive.comp_add, add_comp, cancel_epi, cancel_mono
-/
noncomputable def cocycle₁ : Cocycle Q K 1 :=
  Cocycle.mk (cochain₁ sq hsq hQ hK) 2 (by simp) (by
    have : Epi π := Cofork.IsColimit.epi hQ
    have : Mono ι := Fork.IsLimit.mono hK
    ext n _ rfl
    have := Cochain.congr_v ((cocycle₁' sq hsq).δ_eq_zero 2) n _ rfl
    rw [Cochain.zero_v]; rw [δ_v _ _ (by simp) _ _ _ _ (n + 1) _ (by lia) rfl]; rw [Int.negOnePow_even 2 ⟨1]; rw [by simp⟩]; rw [one_smul] at this ⊢
    rwa [← cancel_mono (ι.f (n + 2)), ← cancel_epi (π.f n),
      Preadditive.add_comp, Category.assoc, Category.assoc, Preadditive.comp_add,
      HomologicalComplex.Hom.comm_assoc,
      π_f_cochain₁_v_ι_f, zero_comp, comp_zero, ← ι.comm,
      π_f_cochain₁_v_ι_f_assoc])

/--
lemma `comp_coe_cocycle₁_comp` / 引理 `comp_coe_cocycle₁_comp`

English:
lemma comp_coe_cocycle₁_comp
  proof: by
  ext n m hnm
  simp [cocycle₁]

中文:
引理 comp_coe_cocycle₁_comp
  证明: by
  ext n m hnm
  simp [cocycle₁]
-/
lemma comp_coe_cocycle₁_comp :
    (Cochain.ofHom π).comp ((cocycle₁ sq hsq hQ hK).1.comp (.ofHom ι)
        (add_zero 1)) (zero_add 1) =
      (cocycle₁' sq hsq).1 := by
  ext n m hnm
  simp [cocycle₁]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `hasLift` / 引理 `hasLift`

English:
lemma hasLift
  given: (α : Cochain Q K 0) (hα : δ 0 1 α = (cocycle₁ sq hsq hQ hK).1)
  proof: by
    replace hα : (Cochain.ofHom π).comp ((δ 0 1 α).comp (.ofHom ι) (add_zero 1)) (zero_add 1) =
        (cocycle₁' sq hsq).1 := by
      rw [← comp_coe_cocycle₁_comp sq hsq hQ hK]; rw [hα]
    let l : Cocycle B X 0 :=
      Cocycle.mk (cochain₀ sq hsq -
        (Cochain.ofHom π).comp
          (α.comp (.ofHom ι) (add_zero 0)) (zero_add 0)) 1 (by simp) (by
            ext p _ rfl
            replace hα := Cochain.congr_v hα p _ rfl
            simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.comp_zero_cochain_v,
              δ_zero_cochain_v, Preadditive.sub_comp, Category.assoc, Preadditive.comp_sub,
              HomologicalComplex.Hom.comm_assoc, cocycle₁', Cocycle.mk_coe, Cochain.ofHoms_v,
              HomologicalComplex.eval_obj, HomologicalComplex.eval_map] at hα
            simp [hα])
    exact ⟨{
      l := l.homOf
      fac_left := by
        ext n
        have h₁ : i.f n ≫ π.f n = 0 := by
          simp [← HomologicalComplex.comp_f, hπ]
        have h₂ := (hsq n).fac_left
        dsimp at h₁ h₂
        simp [l, reassoc_of% h₁, h₂]
      fac_right := by
        ext n
        have : ι.f n ≫ p.f n = 0 := by
          simp [← HomologicalComplex.comp_f, hι]
        simpa [l, this] using (hsq n).fac_right }⟩

中文:
引理 hasLift
  条件: (α : Cochain Q K 0) (hα : δ 0 1 α = (cocycle₁ sq hsq hQ hK).1)
  证明: by
    replace hα : (Cochain.ofHom π).comp ((δ 0 1 α).comp (.ofHom ι) (add_zero 1)) (zero_add 1) =
        (cocycle₁' sq hsq).1 := by
      rw [← comp_coe_cocycle₁_comp sq hsq hQ hK]; rw [hα]
    let l : Cocycle B X 0 :=
      Cocycle.mk (cochain₀ sq hsq -
        (Cochain.ofHom π).comp
          (α.comp (.ofHom ι) (add_zero 0)) (zero_add 0)) 1 (by simp) (by
            ext p _ rfl
            replace hα := Cochain.congr_v hα p _ rfl
            simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.comp_zero_cochain_v,
              δ_zero_cochain_v, Preadditive.sub_comp, Category.assoc, Preadditive.comp_sub,
              HomologicalComplex.Hom.comm_assoc, cocycle₁', Cocycle.mk_coe, Cochain.ofHoms_v,
              HomologicalComplex.eval_obj, HomologicalComplex.eval_map] at hα
            simp [hα])
    exact ⟨{
      l := l.homOf
      fac_left := by
        ext n
        have h₁ : i.f n ≫ π.f n = 0 := by
          simp [← HomologicalComplex.comp_f, hπ]
        have h₂ := (hsq n).fac_left
        dsimp at h₁ h₂
        simp [l, reassoc_of% h₁, h₂]
      fac_right := by
        ext n
        have : ι.f n ≫ p.f n = 0 := by
          simp [← HomologicalComplex.comp_f, hι]
        simpa [l, this] using (hsq n).fac_right }⟩

Depends on / 依赖: Catego, Cochain, Cochain.comp_zero_cochain_v, Cochain.congr_v, Cochain.ofHom, Cochain.ofHom_v, Cochain.zero_cochain_comp_v, Cocycle, Cocycle.mk, Preadditive, Preadditive.sub_comp, add_zero, comp_zero_cochain_v, congr_v, ofHom_v, replace, sub_comp, zero_add, zero_cochain_comp_v
-/
lemma hasLift (α : Cochain Q K 0) (hα : δ 0 1 α = (cocycle₁ sq hsq hQ hK).1) :
    sq.HasLift where
  exists_lift := by
    replace hα : (Cochain.ofHom π).comp ((δ 0 1 α).comp (.ofHom ι) (add_zero 1)) (zero_add 1) =
        (cocycle₁' sq hsq).1 := by
      rw [← comp_coe_cocycle₁_comp sq hsq hQ hK]; rw [hα]
    let l : Cocycle B X 0 :=
      Cocycle.mk (cochain₀ sq hsq -
        (Cochain.ofHom π).comp
          (α.comp (.ofHom ι) (add_zero 0)) (zero_add 0)) 1 (by simp) (by
            ext p _ rfl
            replace hα := Cochain.congr_v hα p _ rfl
            simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.comp_zero_cochain_v,
              δ_zero_cochain_v, Preadditive.sub_comp, Category.assoc, Preadditive.comp_sub,
              HomologicalComplex.Hom.comm_assoc, cocycle₁', Cocycle.mk_coe, Cochain.ofHoms_v,
              HomologicalComplex.eval_obj, HomologicalComplex.eval_map] at hα
            simp [hα])
    exact ⟨{
      l := l.homOf
      fac_left := by
        ext n
        have h₁ : i.f n ≫ π.f n = 0 := by
          simp [← HomologicalComplex.comp_f, hπ]
        have h₂ := (hsq n).fac_left
        dsimp at h₁ h₂
        simp [l, reassoc_of% h₁, h₂]
      fac_right := by
        ext n
        have : ι.f n ≫ p.f n = 0 := by
          simp [← HomologicalComplex.comp_f, hι]
        simpa [l, this] using (hsq n).fac_right }⟩

end Lifting

end CochainComplex
