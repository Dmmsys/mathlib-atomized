/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Center

/-!
# Group actions on projectivization

Show that (among other groups), the general linear group
and the special linear groups of `V` act on `ℙ K V`.

Prove that these actions are 2-transitive.

## TODO

Generalize to the special linear group over a division ring.

-/

@[expose] public section

open scoped LinearAlgebra.Projectivization Matrix

namespace Projectivization

section DivisionRing

variable {G K V : Type*} [AddCommGroup V] [DivisionRing K] [Module K V]
  [Group G] [DistribMulAction G V] [SMulCommClass G K V]

set_option backward.isDefEq.respectTransparency false in
/-- Any group acting `K`-linearly on `V` (such as the general linear group) acts on `ℙ V`. -/
@[simps -isSimp]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction G (ℙ K V)
  body: x.map (DistribMulAction.toModuleEnd _ _ g)
    (DistribMulAction.toLinearEquiv _ _ g).injective
  one_smul x := show map _ _ _ = _ by simp [map_one, Module.End.one_eq_id]
  mul_smul g g' x := show map _ _ _ = map _ _ (map _ _ _) by
    simp_rw [map_mul, Module.End.mul_eq_comp]
    rw [map_comp]; rw 

中文:
实例 :
  签名: 乘法作用 G (ℙ K V)
  定义体: x.map (DistribMulAction.toModuleEnd _ _ g)
    (DistribMulAction.toLinearEquiv _ _ g).injective
  one_smul x := show map _ _ _ = _ by simp [map_one, Module.End.one_eq_id]
  mul_smul g g' x := show map _ _ _ = map _ _ (map _ _ _) by
    simp_rw [map_mul, Module.End.mul_eq_comp]
    rw [map_comp]; rw 

Depends on / 依赖: DistribMulAction, DistribMulAction.toModuleEnd, toModuleEnd, x.map
-/
instance : MulAction G (ℙ K V) where
  smul g x := x.map (DistribMulAction.toModuleEnd _ _ g)
    (DistribMulAction.toLinearEquiv _ _ g).injective
  one_smul x := show map _ _ _ = _ by simp [map_one, Module.End.one_eq_id]
  mul_smul g g' x := show map _ _ _ = map _ _ (map _ _ _) by
    simp_rw [map_mul, Module.End.mul_eq_comp]
    rw [map_comp]; rw [Function.comp_apply]

/--
lemma `generalLinearGroup_smul_def` / 引理 `generalLinearGroup_smul_def`

English:
lemma generalLinearGroup_smul_def
  given: (g : LinearMap.GeneralLinearGroup K V) (x : ℙ K V)
  proof: by
  rfl

中文:
引理 generalLinearGroup_smul_def
  条件: (g : 线性映射.GeneralLinearGroup K V) (x : ℙ K V)
  证明: by
  rfl
-/
lemma generalLinearGroup_smul_def (g : LinearMap.GeneralLinearGroup K V) (x : ℙ K V) :
    g • x = x.map g.toLinearEquiv.toLinearMap g.toLinearEquiv.injective := by
  rfl

/--
lemma `matrixSpecialLinearGroup_smul_def` / 引理 `matrixSpecialLinearGroup_smul_def`

English:
lemma matrixSpecialLinearGroup_smul_def
  statement: {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
  proof: by
  rfl

@[simp]

中文:
引理 matrixSpecialLinearGroup_smul_def
  结论: {ι F : 类型} [有限类型 ι] [DecidableEq ι] [域 F]
  证明: by
  rfl

@[simp]
-/
lemma matrixSpecialLinearGroup_smul_def {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (g : Matrix.SpecialLinearGroup ι F) (x : ℙ F (ι -> F)) :
    g • x = g.toLin'_equiv • x := by
  rfl

@[simp]
/--
lemma `smul_mk` / 引理 `smul_mk`

English:
lemma smul_mk
  given: (g : G) {v : V} (hv : v != 0)
  proof: rfl

中文:
引理 smul_mk
  条件: (g : G) {v : V} (hv : v != 0)
  证明: rfl
-/
lemma smul_mk (g : G) {v : V} (hv : v != 0) :
    g • mk K v hv = mk K (g • v) ((smul_ne_zero_iff_ne g).mpr hv) :=
  rfl

section transitivity

open MulAction FiniteDimensional LinearEquiv

variable (K V) in
/--
Instance `linearEquiv_is_two_pretransitive` / 实例 `linearEquiv_is_two_pretransitive`

English:
instance linearEquiv_is_two_pretransitive
  signature: :
  body: by
  rw [is_two_pretransitive_iff]
  intro D D' E E' hD hE
  have qD {D D' : ℙ K V} (hD : LinearIndependent K ![D.rep, D'.rep]) :
    hD.linearCombinationEquiv (Finsupp.single 0 1) = D.rep := by simp
  have qD' {D D' : ℙ K V} (hD : LinearIndependent K ![D.rep, D'.rep]) :
    hD.linearCombinationEqui

中文:
实例 linearEquiv_is_two_pretransitive
  签名: :
  定义体: by
  rw [is_two_pretransitive_iff]
  intro D D' E E' hD hE
  have qD {D D' : ℙ K V} (hD : LinearIndependent K ![D.rep, D'.rep]) :
    hD.linearCombinationEquiv (Finsupp.single 0 1) = D.rep := by simp
  have qD' {D D' : ℙ K V} (hD : LinearIndependent K ![D.rep, D'.rep]) :
    hD.linearCombinationEqui

Depends on / 依赖: D.rep, FiniteDimensional, Finsupp, Finsupp.single, LinearIndependent, Set.range, Submodule, Submodule.span, hD.linearCombinationEquiv, hD.linearCombinationEquiv.symm, hE.linearCombinationEquiv, is_two_pretransitive_iff, linearCombinationEquiv, linearIndependent_pair_iff_ne, single
-/
instance linearEquiv_is_two_pretransitive :
    IsMultiplyPretransitive (V ≃ₗ[K] V) (ℙ K V) 2 := by
  rw [is_two_pretransitive_iff]
  intro D D' E E' hD hE
  have qD {D D' : ℙ K V} (hD : LinearIndependent K ![D.rep, D'.rep]) :
    hD.linearCombinationEquiv (Finsupp.single 0 1) = D.rep := by simp
  have qD' {D D' : ℙ K V} (hD : LinearIndependent K ![D.rep, D'.rep]) :
    hD.linearCombinationEquiv (Finsupp.single 1 1) = D'.rep := by simp
  rw [← linearIndependent_pair_iff_ne] at hD hE
  let f := hD.linearCombinationEquiv.symm ≪≫ₗ hE.linearCombinationEquiv
  have : FiniteDimensional K (Submodule.span K (Set.range ![D.rep, D'.rep])) :=
    span_of_finite K (Set.finite_range _)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  use g
  constructor
  · rw [← mk_rep D, ← mk_rep E, smul_mk, mk_eq_mk_iff]
    use 1
    simp only [one_smul, LinearEquiv.smul_def, ← qD hD, ← hg, ← qD hE]
    simp [f]
  · rw [← mk_rep D', ← mk_rep E', smul_mk, mk_eq_mk_iff]
    use 1
    simp only [one_smul, LinearEquiv.smul_def, ← qD' hD, ← hg, ← qD' hE]
    simp [f]

variable (K V) in
/--
Instance `generalLinearGroup_is_two_pretransitive` / 实例 `generalLinearGroup_is_two_pretransitive`

English:
instance generalLinearGroup_is_two_pretransitive
  signature: :
  body: by
  let f : ℙ K V ->ₑ[LinearMap.GeneralLinearGroup.ofLinearEquiv (R := K) (M := V)] ℙ K V := {
    toFun := id
    map_smul' e D := by
      simp only [id_eq]
      rw [← mk_rep D]; rw [smul_mk]; rw [smul_mk]
      dsimp }
  exact IsPretransitive.of_embedding (f := f) Function.surjective_id

中文:
实例 generalLinearGroup_is_two_pretransitive
  签名: :
  定义体: by
  let f : ℙ K V ->ₑ[LinearMap.GeneralLinearGroup.ofLinearEquiv (R := K) (M := V)] ℙ K V := {
    toFun := id
    map_smul' e D := by
      simp only [id_eq]
      rw [← mk_rep D]; rw [smul_mk]; rw [smul_mk]
      dsimp }
  exact IsPretransitive.of_embedding (f := f) Function.surjective_id

Depends on / 依赖: Function, Function.surjective_id, GeneralLinearGroup, IsPretransitive, IsPretransitive.of_embedding, LinearMap, LinearMap.GeneralLinearGroup.ofLinearEquiv, id_eq, map_smul, mk_rep, ofLinearEquiv, of_embedding, smul_mk, surjective_id
-/
instance generalLinearGroup_is_two_pretransitive :
    IsMultiplyPretransitive (LinearMap.GeneralLinearGroup K V) (ℙ K V) 2 := by
  let f : ℙ K V ->ₑ[LinearMap.GeneralLinearGroup.ofLinearEquiv (R := K) (M := V)] ℙ K V := {
    toFun := id
    map_smul' e D := by
      simp only [id_eq]
      rw [← mk_rep D]; rw [smul_mk]; rw [smul_mk]
      dsimp }
  exact IsPretransitive.of_embedding (f := f) Function.surjective_id

end transitivity

end DivisionRing

section Field

open MulAction LinearEquiv SpecialLinearGroup

variable {K V : Type*} [AddCommGroup V] [Field K] [Module K V]

/--
theorem `specialLinearGroup_smul_def` / 定理 `specialLinearGroup_smul_def`

English:
theorem specialLinearGroup_smul_def
  given: (g : SpecialLinearGroup K V) (D : ℙ K V)
  proof: rfl

中文:
定理 specialLinearGroup_smul_def
  条件: (g : SpecialLinearGroup K V) (D : ℙ K V)
  证明: rfl
-/
theorem specialLinearGroup_smul_def (g : SpecialLinearGroup K V) (D : ℙ K V) :
    g • D = g.toLinearEquiv • D := rfl

variable (K V) in
/--
Instance `specialLinearGroup_is_two_pretransitive` / 实例 `specialLinearGroup_is_two_pretransitive`

English:
instance specialLinearGroup_is_two_pretransitive
  signature: :
  body: by
  have := linearEquiv_is_two_pretransitive K V
  rw [is_two_pretransitive_iff] at this ⊢
  intro D D' E E' hD hE
  obtain ⟨g, gD, gE⟩ := this hD hE
  by_cases hV : FiniteDimensional K V
  · suffices forall a : Kˣ, exists h : V ≃ₗ[K] V, h.det = a ∧ h • D = D ∧ h • D' = D' by
      obtain ⟨h, hdet,

中文:
实例 specialLinearGroup_is_two_pretransitive
  签名: :
  定义体: by
  have := linearEquiv_is_two_pretransitive K V
  rw [is_two_pretransitive_iff] at this ⊢
  intro D D' E E' hD hE
  obtain ⟨g, gD, gE⟩ := this hD hE
  by_cases hV : FiniteDimensional K V
  · suffices forall a : Kˣ, exists h : V ≃ₗ[K] V, h.det = a ∧ h • D = D ∧ h • D' = D' by
      obtain ⟨h, hdet,

Depends on / 依赖: FiniteDimensional, g.det, h.det, is_two_pretransitive_iff, linearEquiv_is_two_pretransitive, linearIndepOn_pair, linearIndependent_pair_iff_ne, mul_smul, specialLinearGroup_smul_def, toLinearEquiv_eq_coe
-/
instance specialLinearGroup_is_two_pretransitive :
    IsMultiplyPretransitive (SpecialLinearGroup K V) (ℙ K V) 2 := by
  have := linearEquiv_is_two_pretransitive K V
  rw [is_two_pretransitive_iff] at this ⊢
  intro D D' E E' hD hE
  obtain ⟨g, gD, gE⟩ := this hD hE
  by_cases hV : FiniteDimensional K V
  · suffices forall a : Kˣ, exists h : V ≃ₗ[K] V, h.det = a ∧ h • D = D ∧ h • D' = D' by
      obtain ⟨h, hdet, hD, hE⟩ := this (g.det)⁻¹
      use ⟨g * h, by simp [hdet]⟩
      simp [specialLinearGroup_smul_def, toLinearEquiv_eq_coe, mul_smul, gD, hD, gE, hE]
    intro a
    rw [← linearIndependent_pair_iff_ne] at hD
    have := linearIndepOn_pair D D'
    let s := (linearIndepOn_pair D D').extend (Set.subset_univ _)
    let b : Module.Basis s K V := Module.Basis.extend this
    rw [← mk_rep D]; rw [← mk_rep D']
    have hD_mem : D.rep in s := LinearIndepOn.subset_extend _ _ (by simp)
    have hD'_mem : D'.rep in s := LinearIndepOn.subset_extend _ _ (by simp)
    refine ⟨dilatransvection (f := b.coord ⟨D.rep, hD_mem⟩)
      (v := (a.val - 1) • b ⟨D.rep, hD_mem⟩) (by simp), ?_, ?_, ?_⟩
    · simp [← Units.val_inj, coe_det, LinearMap.transvection.det]
    · rw [smul_mk, mk_eq_mk_iff, LinearEquiv.smul_def]
      use a
      rw [← coe_coe]; rw [dilatransvection.coe_toLinearMap]; rw [LinearMap.transvection.apply]; rw [Module.Basis.coord_apply]
      suffices (b.repr D.rep) ⟨D.rep, hD_mem⟩ = 1 by
        rw [this]; rw [Module.Basis.extend_apply_self]; rw [Units.smul_def]
        module
      nth_rewrite 1 [show D.rep = (⟨D.rep, hD_mem⟩ : s) by rfl]
      rw [← Module.Basis.extend_apply_self]; rw [Module.Basis.repr_self]
      simp
    · rw [smul_mk, mk_eq_mk_iff, LinearEquiv.smul_def]
      use 1
      rw [one_smul]; rw [← coe_coe]; rw [dilatransvection.coe_toLinearMap]; rw [LinearMap.transvection.apply]; rw [Module.Basis.coord_apply]
      suffices (b.repr D'.rep) ⟨D.rep, hD_mem⟩ = 0 by
        rw [Module.Basis.extend_apply_self]
        simp [this]
      nth_rewrite 1 [show D'.rep = (⟨D'.rep, hD'_mem⟩ : s) by rfl]
      rw [← Module.Basis.extend_apply_self]; rw [Module.Basis.repr_self]
      apply Finsupp.single_eq_of_ne
      simp only [ne_eq, ← Subtype.coe_inj]
      intro h
      apply Fin.zero_ne_one
      apply hD.injective
      simp [h]
  use ⟨g, by
    rw [← Units.val_inj]; rw [coe_det]
    apply LinearMap.det_eq_one_of_not_module_finite hV⟩
  simp [← gD, ← gE, specialLinearGroup_smul_def, toLinearEquiv_eq_coe]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPreprimitive (SpecialLinearGroup K V) (ℙ K V)
  body: isPreprimitive_of_is_two_pretransitive inferInstance

中文:
实例 :
  签名: 是Preprimitive (SpecialLinearGroup K V) (ℙ K V)
  定义体: isPreprimitive_of_is_two_pretransitive inferInstance

Depends on / 依赖: isPreprimitive_of_is_two_pretransitive
-/
instance : IsPreprimitive (SpecialLinearGroup K V) (ℙ K V) :=
  isPreprimitive_of_is_two_pretransitive inferInstance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMultiplyPretransitive (Matrix.SpecialLinearGroup ι K) (ℙ K (ι -> K)) 2
  body: let φ : SpecialLinearGroup K (ι -> K) ->* Matrix.SpecialLinearGroup ι K :=
    Matrix.SpecialLinearGroup.toLin'_equiv.symm.toMonoidHom
  let f : ℙ K (ι -> K) ->ₑ[φ] ℙ K (ι -> K) :=
    { toFun := id
      map_smul' g D := by simp [φ, matrixSpecialLinearGroup_smul_def]}
  IsPretransitive.of_embedding

中文:
实例 :
  签名: IsMultiplyPretransitive (矩阵.SpecialLinearGroup ι K) (ℙ K (ι -> K)) 2
  定义体: let φ : SpecialLinearGroup K (ι -> K) ->* Matrix.SpecialLinearGroup ι K :=
    Matrix.SpecialLinearGroup.toLin'_equiv.symm.toMonoidHom
  let f : ℙ K (ι -> K) ->ₑ[φ] ℙ K (ι -> K) :=
    { toFun := id
      map_smul' g D := by simp [φ, matrixSpecialLinearGroup_smul_def]}
  IsPretransitive.of_embedding

Depends on / 依赖: Function, Function.surjective_id, IsPretransitive, IsPretransitive.of_embedding, Matrix, Matrix.SpecialLinearGroup, Matrix.SpecialLinearGroup.toLin, SpecialLinearGroup, _equiv, _equiv.symm.toMonoidHom, map_smul, matrixSpecialLinearGroup_smul_def, of_embedding, surjective_id, toMonoidHom
-/
instance : IsMultiplyPretransitive (Matrix.SpecialLinearGroup ι K) (ℙ K (ι -> K)) 2 :=
  let φ : SpecialLinearGroup K (ι -> K) ->* Matrix.SpecialLinearGroup ι K :=
    Matrix.SpecialLinearGroup.toLin'_equiv.symm.toMonoidHom
  let f : ℙ K (ι -> K) ->ₑ[φ] ℙ K (ι -> K) :=
    { toFun := id
      map_smul' g D := by simp [φ, matrixSpecialLinearGroup_smul_def]}
  IsPretransitive.of_embedding (f := f) Function.surjective_id

/--
Instance `prePrimitive_SL` / 实例 `prePrimitive_SL`

English:
instance prePrimitive_SL
  signature: : IsPreprimitive (Matrix.SpecialLinearGroup ι K) (ℙ K (ι -> K))
  body: isPreprimitive_of_is_two_pretransitive inferInstance

中文:
实例 prePrimitive_SL
  签名: : 是Preprimitive (矩阵.SpecialLinearGroup ι K) (ℙ K (ι -> K))
  定义体: isPreprimitive_of_is_two_pretransitive inferInstance

Depends on / 依赖: isPreprimitive_of_is_two_pretransitive
-/
instance prePrimitive_SL : IsPreprimitive (Matrix.SpecialLinearGroup ι K) (ℙ K (ι -> K)) :=
  isPreprimitive_of_is_two_pretransitive inferInstance

/--
lemma `SL_mulAction_ker` / 引理 `SL_mulAction_ker`

English:
lemma SL_mulAction_ker
  proof: by
  ext m
  simp only [MonoidHom.mem_ker, toPermHom_apply, Equiv.Perm.one_def, DFunLike.ext_iff, toPerm_apply,
    Equiv.refl_apply, Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨fun hm => ?_, fun ⟨r, hr1, hr2⟩ l => ?_⟩
  · set f : (ι -> K) ->ₗ[K] ι -> K := (Matrix.SpecialLinearGroup.toLin' m

中文:
引理 SL_mulAction_ker
  证明: by
  ext m
  simp only [MonoidHom.mem_ker, toPermHom_apply, Equiv.Perm.one_def, DFunLike.ext_iff, toPerm_apply,
    Equiv.refl_apply, Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨fun hm => ?_, fun ⟨r, hr1, hr2⟩ l => ?_⟩
  · set f : (ι -> K) ->ₗ[K] ι -> K := (Matrix.SpecialLinearGroup.toLin' m

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Equiv.Perm.one_def, Equiv.refl_apply, InnerRegular, InnerRegularCompactLTTop, LinearIndependent, LinearIndependent.pair_iff, Matrix, Matrix.SpecialLinearGroup.mem_center_iff, Matrix.SpecialLinearGroup.toLin, MonoidHom, MonoidHom.mem_ker, SpecialLinearGroup, exists_eq_smul_id_of_forall_notLinearIndependent, ext_iff, f.exists_eq_smul_id_of_forall_notLinearIndependent, linearIndependent_fin2, mem_center_iff, mem_ker
-/
lemma SL_mulAction_ker :
    (MulAction.toPermHom (Matrix.SpecialLinearGroup ι K) (ℙ K (ι -> K))).ker =
      Subgroup.center (Matrix.SpecialLinearGroup ι K) := by
  ext m
  simp only [MonoidHom.mem_ker, toPermHom_apply, Equiv.Perm.one_def, DFunLike.ext_iff, toPerm_apply,
    Equiv.refl_apply, Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨fun hm => ?_, fun ⟨r, hr1, hr2⟩ l => ?_⟩
  · set f : (ι -> K) ->ₗ[K] ι -> K := (Matrix.SpecialLinearGroup.toLin' m).toLinearMap with hf
    obtain ⟨a, ha⟩ := f.exists_eq_smul_id_of_forall_notLinearIndependent fun (v : ι -> K) => by
      by_cases hv : v = 0
      · simp [hv, linearIndependent_fin2]
      · simpa [LinearIndependent.pair_iff' hv, mk_eq_mk_iff'] using! hm (.mk K v hv)
    have hscalar : m.1 = Matrix.scalar ι a := calc
      m.1 = LinearMap.toMatrix' f := by
        rw [hf]; rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap]; rw [LinearMap.toMatrix'_toLin']
      _ = (algebraMap K (Module.End K (ι -> K)) a).toMatrix' := congrArg LinearMap.toMatrix' ha
      _ = Matrix.scalar ι a := LinearMap.toMatrix'_algebraMap a
    exact ⟨a, by simpa [hscalar] using m.2, hscalar.symm⟩
  · induction l using Projectivization.ind with | _ v hv =>
    simp only [smul_mk, mk_eq_mk_iff']
    use r
    change _ = m.1 • v
    simp [← hr2]

/--
Definition of `PSLAction.toPermHom` / `PSLAction.toPermHom` 的定义

English:
definition PSLAction.toPermHom
  signature: :
  body: QuotientGroup.lift _ (MulAction.toPermHom _ _) (le_of_eq SL_mulAction_ker.symm)

中文:
定义 PSLAction.toPermHom
  签名: :
  定义体: QuotientGroup.lift _ (MulAction.toPermHom _ _) (le_of_eq SL_mulAction_ker.symm)

Depends on / 依赖: MulAction, MulAction.toPermHom, QuotientGroup, QuotientGroup.lift, SL_mulAction_ker, SL_mulAction_ker.symm, le_of_eq, toPermHom
-/
def PSLAction.toPermHom :
    Matrix.ProjectiveSpecialLinearGroup ι K ->* Equiv.Perm (ℙ K (ι -> K)) :=
  QuotientGroup.lift _ (MulAction.toPermHom _ _) (le_of_eq SL_mulAction_ker.symm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι -> K))
  body: MulAction.compHom _ PSLAction.toPermHom

中文:
实例 :
  签名: 乘法作用 (矩阵.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι -> K))
  定义体: MulAction.compHom _ PSLAction.toPermHom

Depends on / 依赖: MulAction, MulAction.compHom, PSLAction, PSLAction.toPermHom, compHom, toPermHom
-/
instance : MulAction (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι -> K)) :=
  MulAction.compHom _ PSLAction.toPermHom

/--
lemma `_root_.Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk` / 引理 `_root_.Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk`

English:
lemma _root_.Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk
  statement: (g : Matrix.SpecialLinearGroup ι K)
  proof: rfl

中文:
引理 _root_.矩阵.ProjectiveSpecialLinearGroup.smul_proj_mk
  结论: (g : 矩阵.SpecialLinearGroup ι K)
  证明: rfl
-/
lemma _root_.Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk (g : Matrix.SpecialLinearGroup ι K)
    (p : ℙ K (ι -> K)) : (g : Matrix.ProjectiveSpecialLinearGroup ι K) • p = g • p := rfl

/--
theorem `_root_.Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective` / 定理 `_root_.Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective`

English:
theorem _root_.Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective
  proof: by
  rw [injective_iff_map_eq_one]
  intro g hg
  rwa [← MonoidHom.mem_ker, PSLAction.toPermHom,
    QuotientGroup.ker_lift, SL_mulAction_ker, QuotientGroup.map_mk'_self,
    Subgroup.mem_bot] at hg

中文:
定理 _root_.矩阵.ProjectiveSpecialLinearGroup.toPermHom_injective
  证明: by
  rw [injective_iff_map_eq_one]
  intro g hg
  rwa [← MonoidHom.mem_ker, PSLAction.toPermHom,
    QuotientGroup.ker_lift, SL_mulAction_ker, QuotientGroup.map_mk'_self,
    Subgroup.mem_bot] at hg

Depends on / 依赖: ENNReal, ENNReal.exists_lt_add_of_lt_add, K.trans_le, MeasurableSet, MeasurableSet.exists_lt_isCompact, Measure, Measure.coe_add, MonoidHom, MonoidHom.mem_ker, PSLAction, PSLAction.toPermHom, Pi.add_apply, QuotientGroup, QuotientGroup.ker_lift, QuotientGroup.map_mk, SL_mulAction_ker, Subgroup, Subgroup.mem_bot, _self, add_apply
-/
theorem _root_.Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective :
    Function.Injective (PSLAction.toPermHom (K := K) (ι := ι)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rwa [← MonoidHom.mem_ker, PSLAction.toPermHom,
    QuotientGroup.ker_lift, SL_mulAction_ker, QuotientGroup.map_mk'_self,
    Subgroup.mem_bot] at hg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι -> K))
  body: faithfulSMul_iff.2 fun g hg =>
Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective Equiv.ext fun x => by
      simpa using! hg x

中文:
实例 :
  签名: 忠实标量乘法 (矩阵.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι -> K))
  定义体: faithfulSMul_iff.2 fun g hg =>
Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective Equiv.ext fun x => by
      simpa using! hg x

Depends on / 依赖: Equiv.ext, Finset, Finset.induction, Finset.sum_empty, Finset.sum_insert, Matrix, Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective, ProjectiveSpecialLinearGroup, classical, faithfulSMul_iff, infer_instance, insert, not_false_eq_true, sum_empty, sum_insert, toPermHom_injective
-/
instance : FaithfulSMul (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι -> K)) :=
  faithfulSMul_iff.2 fun g hg =>
Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective Equiv.ext fun x => by
      simpa using! hg x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPreprimitive (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι -> K))
  body: @MulAction.IsPreprimitive.of_surjective _ _ _ _ _ _ _ _ (QuotientGroup.mk' _)
    {toFun := id, map_smul' := by intros; simp; rfl} (prePrimitive_SL (ι := ι) (K := K))
    Function.surjective_id

中文:
实例 :
  签名: 是Preprimitive (矩阵.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι -> K))
  定义体: @MulAction.IsPreprimitive.of_surjective _ _ _ _ _ _ _ _ (QuotientGroup.mk' _)
    {toFun := id, map_smul' := by intros; simp; rfl} (prePrimitive_SL (ι := ι) (K := K))
    Function.surjective_id

Depends on / 依赖: ENNReal, ENNReal.summable.hasSum, Finset, Finset.sum_apply, Function, Function.surjective_id, IsPreprimitive, K.trans_le, MeasurableSet, MeasurableSet.exists_lt_isCompact, Measure, Measure.sum, Measure.sum_apply, MulAction, MulAction.IsPreprimitive.of_surjective, QuotientGroup, QuotientGroup.mk, Tendsto, coe_finsetSum, exists_lt_isCompact
-/
instance : IsPreprimitive (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι -> K)) :=
  @MulAction.IsPreprimitive.of_surjective _ _ _ _ _ _ _ _ (QuotientGroup.mk' _)
    {toFun := id, map_smul' := by intros; simp; rfl} (prePrimitive_SL (ι := ι) (K := K))
    Function.surjective_id

open MatrixGroups Matrix.ProjGenLinGroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction PGL(ι, K) (ℙ K (ι -> K))
  body: mulActionOfGL fun u => ind fun v hv => by
    simp only [smul_mk, mk_eq_mk_iff]
    exact ⟨u, by simp [Units.smul_def]⟩

@[simp]

中文:
实例 :
  签名: 乘法作用 PGL(ι, K) (ℙ K (ι -> K))
  定义体: mulActionOfGL fun u => ind fun v hv => by
    simp only [smul_mk, mk_eq_mk_iff]
    exact ⟨u, by simp [Units.smul_def]⟩

@[simp]

Depends on / 依赖: Units.smul_def, mk_eq_mk_iff, mulActionOfGL, smul_def, smul_mk
-/
instance : MulAction PGL(ι, K) (ℙ K (ι -> K)) :=
  mulActionOfGL fun u => ind fun v hv => by
    simp only [smul_mk, mk_eq_mk_iff]
    exact ⟨u, by simp [Units.smul_def]⟩

@[simp]
/--
lemma `PGL.mk_smul_mk` / 引理 `PGL.mk_smul_mk`

English:
lemma PGL.mk_smul_mk
  given: (g : GL ι K) {v : ι -> K} (hv : v != 0)
  proof: rfl

中文:
引理 PGL.mk_smul_mk
  条件: (g : GL ι K) {v : ι -> K} (hv : v != 0)
  证明: rfl
-/
lemma PGL.mk_smul_mk (g : GL ι K) {v : ι -> K} (hv : v != 0) :
    (.mk g : PGL(ι, K)) • mk K v hv = mk K (g • v) (smul_ne_zero_iff_ne g|>.2 hv) := rfl

end Field

end Projectivization
